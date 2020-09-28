                                                                          
                                                                           
                                                                           
                                                                           
                                                                           
                                                                           
                                                                           
                                                                           
                                                                           
                                                                           
                                                                           
                                                                           
                                                                           
                                                                          
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
* Copyright (C) 2013 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/*******************************************************************************
*
* Device     : RX/RX700/RX72N
*
* File Name  : iodefine.h
*
* Abstract   : Definition of I/O Register.
*
* History    : V0.50  (2019-03-15)  [Hardware Manual Revision : 0.50]
*              V1.00C (2019-07-17)  [Hardware Manual Revision : 1.00]
*
* NOTE       : THIS IS A TYPICAL EXAMPLE.
*
*  Copyright(c) 2019 Renesas Electronics Corporation.
*
*********************************************************************************/
/********************************************************************************/
/*                                                                              */
/*  DESCRIPTION : Definition of ICU Register                                    */
/*  CPU TYPE    : RX72N                                                         */
/*                                                                              */
/*  Usage : IR,DTCER,IER,IPR of ICU Register                                    */
/*     The following IR, DTCE, IEN, IPR macro functions simplify usage.         */
/*     The bit access operation is "Bit_Name(interrupt source,name)".           */
/*     A part of the name can be omitted.                                       */
/*     for example :                                                            */
/*       IR(BSC,BUSERR) = 0;     expands to :                                   */
/*         ICU.IR[16].BIT.IR = 0;                                               */
/*                                                                              */
/*       DTCE(ICU,IRQ0) = 1;     expands to :                                   */
/*         ICU.DTCER[64].BIT.DTCE = 1;                                          */
/*                                                                              */
/*       IEN(CMT0,CMI0) = 1;     expands to :                                   */
/*         ICU.IER[0x03].BIT.IEN4 = 1;                                          */
/*                                                                              */
/*       IPR(ICU,SWINT2) = 2;    expands to :                                   */
/*       IPR(ICU,SWI   ) = 2;    // SWINT2,SWINT share IPR level.               */
/*         ICU.IPR[3].BIT.IPR = 2;                                              */
/*                                                                              */
/*  Usage : #pragma interrupt Function_Identifier(vect=**)                      */
/*     The number of vector is "(interrupt source, name)".                      */
/*     for example :                                                            */
/*       #pragma interrupt INT_IRQ0(vect=VECT(ICU,IRQ0))          expands to :  */
/*         #pragma interrupt INT_IRQ0(vect=64)                                  */
/*       #pragma interrupt INT_CMT0_CMI0(vect=VECT(CMT0,CMI0))    expands to :  */
/*         #pragma interrupt INT_CMT0_CMI0(vect=28)                             */
/*                                                                              */
/*  Usage : MSTPCRA,MSTPCRB,MSTPCRC of SYSTEM Register                          */
/*     The bit access operation is "MSTP(name)".                                */
/*     The name that can be used is a macro name defined with "iodefine.h".     */
/*     for example :                                                            */
/*       MSTP(TMR2) = 0;    // TMR2,TMR3,TMR23                    expands to :  */
/*         SYSTEM.MSTPCRA.BIT.MSTPA4  = 0;                                      */
/*       MSTP(SCI0) = 0;    // SCI0,SMCI0                         expands to :  */
/*         SYSTEM.MSTPCRB.BIT.MSTPB31 = 0;                                      */
/*       MSTP(MTU4) = 0;    // MTU,MTU0,MTU1,MTU2,MTU3,MTU4,...   expands to :  */
/*         SYSTEM.MSTPCRA.BIT.MSTPA9  = 0;                                      */
/*       MSTP(TPU4) = 0;    // TPU0,TPU1,TPU2,TPU3,TPU4,TPU5,TPUA expands to :  */
/*         SYSTEM.MSTPCRA.BIT.MSTPA13 = 0;                                      */
/*       MSTP(CMT3) = 0;    // CMT2,CMT3                          expands to :  */
/*         SYSTEM.MSTPCRA.BIT.MSTPA14 = 0;                                      */
/*                                                                              */
/*                                                                              */
/********************************************************************************/
#ifndef __RX72NIODEFINE_HEADER__
#define __RX72NIODEFINE_HEADER__

#define	IEN_BSC_BUSERR		IEN0
#define	IEN_ICU_GROUPIE0	IEN1
#define	IEN_RAM_RAMERR		IEN2
#define	IEN_FCU_FIFERR		IEN5
#define	IEN_FCU_FRDYI		IEN7
#define	IEN_ICU_SWINT2		IEN2
#define	IEN_ICU_SWINT		IEN3
#define	IEN_CMT0_CMI0		IEN4
#define	IEN_CMT1_CMI1		IEN5
#define	IEN_CMTW0_CMWI0		IEN6
#define	IEN_CMTW1_CMWI1		IEN7
#define	IEN_USB0_D0FIFO0	IEN2
#define	IEN_USB0_D1FIFO0	IEN3
#define	IEN_RSPI0_SPRI0		IEN6
#define	IEN_RSPI0_SPTI0		IEN7
#define	IEN_RSPI1_SPRI1		IEN0
#define	IEN_RSPI1_SPTI1		IEN1
#define	IEN_QSPI_SPRI		IEN2
#define	IEN_QSPI_SPTI		IEN3
#define	IEN_SDHI_SBFAI		IEN4
#define	IEN_MMCIF_MBFAI		IEN5
#define	IEN_SSIE0_SSITXI0	IEN6
#define	IEN_SSIE0_SSIRXI0	IEN7
#define	IEN_SSIE1_SSIRTI1	IEN0
#define	IEN_RIIC1_RXI1		IEN2
#define	IEN_RIIC1_TXI1		IEN3
#define	IEN_RIIC0_RXI0		IEN4
#define	IEN_RIIC0_TXI0		IEN5
#define	IEN_RIIC2_RXI2		IEN6
#define	IEN_RIIC2_TXI2		IEN7
#define	IEN_SCI0_RXI0		IEN2
#define	IEN_SCI0_TXI0		IEN3
#define	IEN_SCI1_RXI1		IEN4
#define	IEN_SCI1_TXI1		IEN5
#define	IEN_SCI2_RXI2		IEN6
#define	IEN_SCI2_TXI2		IEN7
#define	IEN_ICU_IRQ0		IEN0
#define	IEN_ICU_IRQ1		IEN1
#define	IEN_ICU_IRQ2		IEN2
#define	IEN_ICU_IRQ3		IEN3
#define	IEN_ICU_IRQ4		IEN4
#define	IEN_ICU_IRQ5		IEN5
#define	IEN_ICU_IRQ6		IEN6
#define	IEN_ICU_IRQ7		IEN7
#define	IEN_ICU_IRQ8		IEN0
#define	IEN_ICU_IRQ9		IEN1
#define	IEN_ICU_IRQ10		IEN2
#define	IEN_ICU_IRQ11		IEN3
#define	IEN_ICU_IRQ12		IEN4
#define	IEN_ICU_IRQ13		IEN5
#define	IEN_ICU_IRQ14		IEN6
#define	IEN_ICU_IRQ15		IEN7
#define	IEN_SCI3_RXI3		IEN0
#define	IEN_SCI3_TXI3		IEN1
#define	IEN_SCI4_RXI4		IEN2
#define	IEN_SCI4_TXI4		IEN3
#define	IEN_SCI5_RXI5		IEN4
#define	IEN_SCI5_TXI5		IEN5
#define	IEN_SCI6_RXI6		IEN6
#define	IEN_SCI6_TXI6		IEN7
#define	IEN_LVD1_LVD1		IEN0
#define	IEN_LVD2_LVD2		IEN1
#define	IEN_USB0_USBR0		IEN2
#define	IEN_RTC_ALM			IEN4
#define	IEN_RTC_PRD			IEN5
#define	IEN_IWDT_IWUNI		IEN7
#define	IEN_WDT_WUNI		IEN0
#define	IEN_PDC_PCDFI		IEN1
#define	IEN_SCI7_RXI7		IEN2
#define	IEN_SCI7_TXI7		IEN3
#define	IEN_SCI8_RXI8		IEN4
#define	IEN_SCI8_TXI8		IEN5
#define	IEN_SCI9_RXI9		IEN6
#define	IEN_SCI9_TXI9		IEN7
#define	IEN_SCI10_RXI10		IEN0
#define	IEN_SCI10_TXI10		IEN1
#define	IEN_ICU_GROUPBE0	IEN2
#define	IEN_ICU_GROUPBL2	IEN3
#define	IEN_RSPI2_SPRI2		IEN4
#define	IEN_RSPI2_SPTI2		IEN5
#define	IEN_ICU_GROUPBL0	IEN6
#define	IEN_ICU_GROUPBL1	IEN7
#define	IEN_ICU_GROUPAL0	IEN0
#define	IEN_ICU_GROUPAL1	IEN1
#define	IEN_SCI11_RXI11		IEN2
#define	IEN_SCI11_TXI11		IEN3
#define	IEN_SCI12_RXI12		IEN4
#define	IEN_SCI12_TXI12		IEN5
#define	IEN_DMAC_DMAC0I		IEN0
#define	IEN_DMAC_DMAC1I		IEN1
#define	IEN_DMAC_DMAC2I		IEN2
#define	IEN_DMAC_DMAC3I		IEN3
#define	IEN_DMAC_DMAC74I	IEN4
#define	IEN_OST_OSTDI		IEN5
#define	IEN_EXDMAC_EXDMAC0I	IEN6
#define	IEN_EXDMAC_EXDMAC1I	IEN7
#define	IEN_PERIB_INTB128	IEN0
#define	IEN_PERIB_INTB129	IEN1
#define	IEN_PERIB_INTB130	IEN2
#define	IEN_PERIB_INTB131	IEN3
#define	IEN_PERIB_INTB132	IEN4
#define	IEN_PERIB_INTB133	IEN5
#define	IEN_PERIB_INTB134	IEN6
#define	IEN_PERIB_INTB135	IEN7
#define	IEN_PERIB_INTB136	IEN0
#define	IEN_PERIB_INTB137	IEN1
#define	IEN_PERIB_INTB138	IEN2
#define	IEN_PERIB_INTB139	IEN3
#define	IEN_PERIB_INTB140	IEN4
#define	IEN_PERIB_INTB141	IEN5
#define	IEN_PERIB_INTB142	IEN6
#define	IEN_PERIB_INTB143	IEN7
#define	IEN_PERIB_INTB144	IEN0
#define	IEN_PERIB_INTB145	IEN1
#define	IEN_PERIB_INTB146	IEN2
#define	IEN_PERIB_INTB147	IEN3
#define	IEN_PERIB_INTB148	IEN4
#define	IEN_PERIB_INTB149	IEN5
#define	IEN_PERIB_INTB150	IEN6
#define	IEN_PERIB_INTB151	IEN7
#define	IEN_PERIB_INTB152	IEN0
#define	IEN_PERIB_INTB153	IEN1
#define	IEN_PERIB_INTB154	IEN2
#define	IEN_PERIB_INTB155	IEN3
#define	IEN_PERIB_INTB156	IEN4
#define	IEN_PERIB_INTB157	IEN5
#define	IEN_PERIB_INTB158	IEN6
#define	IEN_PERIB_INTB159	IEN7
#define	IEN_PERIB_INTB160	IEN0
#define	IEN_PERIB_INTB161	IEN1
#define	IEN_PERIB_INTB162	IEN2
#define	IEN_PERIB_INTB163	IEN3
#define	IEN_PERIB_INTB164	IEN4
#define	IEN_PERIB_INTB165	IEN5
#define	IEN_PERIB_INTB166	IEN6
#define	IEN_PERIB_INTB167	IEN7
#define	IEN_PERIB_INTB168	IEN0
#define	IEN_PERIB_INTB169	IEN1
#define	IEN_PERIB_INTB170	IEN2
#define	IEN_PERIB_INTB171	IEN3
#define	IEN_PERIB_INTB172	IEN4
#define	IEN_PERIB_INTB173	IEN5
#define	IEN_PERIB_INTB174	IEN6
#define	IEN_PERIB_INTB175	IEN7
#define	IEN_PERIB_INTB176	IEN0
#define	IEN_PERIB_INTB177	IEN1
#define	IEN_PERIB_INTB178	IEN2
#define	IEN_PERIB_INTB179	IEN3
#define	IEN_PERIB_INTB180	IEN4
#define	IEN_PERIB_INTB181	IEN5
#define	IEN_PERIB_INTB182	IEN6
#define	IEN_PERIB_INTB183	IEN7
#define	IEN_PERIB_INTB184	IEN0
#define	IEN_PERIB_INTB185	IEN1
#define	IEN_PERIB_INTB186	IEN2
#define	IEN_PERIB_INTB187	IEN3
#define	IEN_PERIB_INTB188	IEN4
#define	IEN_PERIB_INTB189	IEN5
#define	IEN_PERIB_INTB190	IEN6
#define	IEN_PERIB_INTB191	IEN7
#define	IEN_PERIB_INTB192	IEN0
#define	IEN_PERIB_INTB193	IEN1
#define	IEN_PERIB_INTB194	IEN2
#define	IEN_PERIB_INTB195	IEN3
#define	IEN_PERIB_INTB196	IEN4
#define	IEN_PERIB_INTB197	IEN5
#define	IEN_PERIB_INTB198	IEN6
#define	IEN_PERIB_INTB199	IEN7
#define	IEN_PERIB_INTB200	IEN0
#define	IEN_PERIB_INTB201	IEN1
#define	IEN_PERIB_INTB202	IEN2
#define	IEN_PERIB_INTB203	IEN3
#define	IEN_PERIB_INTB204	IEN4
#define	IEN_PERIB_INTB205	IEN5
#define	IEN_PERIB_INTB206	IEN6
#define	IEN_PERIB_INTB207	IEN7
#define	IEN_PERIA_INTA208	IEN0
#define	IEN_PERIA_INTA209	IEN1
#define	IEN_PERIA_INTA210	IEN2
#define	IEN_PERIA_INTA211	IEN3
#define	IEN_PERIA_INTA212	IEN4
#define	IEN_PERIA_INTA213	IEN5
#define	IEN_PERIA_INTA214	IEN6
#define	IEN_PERIA_INTA215	IEN7
#define	IEN_PERIA_INTA216	IEN0
#define	IEN_PERIA_INTA217	IEN1
#define	IEN_PERIA_INTA218	IEN2
#define	IEN_PERIA_INTA219	IEN3
#define	IEN_PERIA_INTA220	IEN4
#define	IEN_PERIA_INTA221	IEN5
#define	IEN_PERIA_INTA222	IEN6
#define	IEN_PERIA_INTA223	IEN7
#define	IEN_PERIA_INTA224	IEN0
#define	IEN_PERIA_INTA225	IEN1
#define	IEN_PERIA_INTA226	IEN2
#define	IEN_PERIA_INTA227	IEN3
#define	IEN_PERIA_INTA228	IEN4
#define	IEN_PERIA_INTA229	IEN5
#define	IEN_PERIA_INTA230	IEN6
#define	IEN_PERIA_INTA231	IEN7
#define	IEN_PERIA_INTA232	IEN0
#define	IEN_PERIA_INTA233	IEN1
#define	IEN_PERIA_INTA234	IEN2
#define	IEN_PERIA_INTA235	IEN3
#define	IEN_PERIA_INTA236	IEN4
#define	IEN_PERIA_INTA237	IEN5
#define	IEN_PERIA_INTA238	IEN6
#define	IEN_PERIA_INTA239	IEN7
#define	IEN_PERIA_INTA240	IEN0
#define	IEN_PERIA_INTA241	IEN1
#define	IEN_PERIA_INTA242	IEN2
#define	IEN_PERIA_INTA243	IEN3
#define	IEN_PERIA_INTA244	IEN4
#define	IEN_PERIA_INTA245	IEN5
#define	IEN_PERIA_INTA246	IEN6
#define	IEN_PERIA_INTA247	IEN7
#define	IEN_PERIA_INTA248	IEN0
#define	IEN_PERIA_INTA249	IEN1
#define	IEN_PERIA_INTA250	IEN2
#define	IEN_PERIA_INTA251	IEN3
#define	IEN_PERIA_INTA252	IEN4
#define	IEN_PERIA_INTA253	IEN5
#define	IEN_PERIA_INTA254	IEN6
#define	IEN_PERIA_INTA255	IEN7

#define	VECT_BSC_BUSERR		16
#define	VECT_ICU_GROUPIE0	17
#define	VECT_RAM_RAMERR		18
#define	VECT_FCU_FIFERR		21
#define	VECT_FCU_FRDYI		23
#define	VECT_ICU_SWINT2		26
#define	VECT_ICU_SWINT		27
#define	VECT_CMT0_CMI0		28
#define	VECT_CMT1_CMI1		29
#define	VECT_CMTW0_CMWI0	30
#define	VECT_CMTW1_CMWI1	31
#define	VECT_USB0_D0FIFO0	34
#define	VECT_USB0_D1FIFO0	35
#define	VECT_RSPI0_SPRI0	38
#define	VECT_RSPI0_SPTI0	39
#define	VECT_RSPI1_SPRI1	40
#define	VECT_RSPI1_SPTI1	41
#define	VECT_QSPI_SPRI		42
#define	VECT_QSPI_SPTI		43
#define	VECT_SDHI_SBFAI		44
#define	VECT_MMCIF_MBFAI	45
#define	VECT_SSIE0_SSITXI0	46
#define	VECT_SSIE0_SSIRXI0	47
#define	VECT_SSIE1_SSIRTI1	48
#define	VECT_RIIC1_RXI1		50
#define	VECT_RIIC1_TXI1		51
#define	VECT_RIIC0_RXI0		52
#define	VECT_RIIC0_TXI0		53
#define	VECT_RIIC2_RXI2		54
#define	VECT_RIIC2_TXI2		55
#define	VECT_SCI0_RXI0		58
#define	VECT_SCI0_TXI0		59
#define	VECT_SCI1_RXI1		60
#define	VECT_SCI1_TXI1		61
#define	VECT_SCI2_RXI2		62
#define	VECT_SCI2_TXI2		63
#define	VECT_ICU_IRQ0		64
#define	VECT_ICU_IRQ1		65
#define	VECT_ICU_IRQ2		66
#define	VECT_ICU_IRQ3		67
#define	VECT_ICU_IRQ4		68
#define	VECT_ICU_IRQ5		69
#define	VECT_ICU_IRQ6		70
#define	VECT_ICU_IRQ7		71
#define	VECT_ICU_IRQ8		72
#define	VECT_ICU_IRQ9		73
#define	VECT_ICU_IRQ10		74
#define	VECT_ICU_IRQ11		75
#define	VECT_ICU_IRQ12		76
#define	VECT_ICU_IRQ13		77
#define	VECT_ICU_IRQ14		78
#define	VECT_ICU_IRQ15		79
#define	VECT_SCI3_RXI3		80
#define	VECT_SCI3_TXI3		81
#define	VECT_SCI4_RXI4		82
#define	VECT_SCI4_TXI4		83
#define	VECT_SCI5_RXI5		84
#define	VECT_SCI5_TXI5		85
#define	VECT_SCI6_RXI6		86
#define	VECT_SCI6_TXI6		87
#define	VECT_LVD1_LVD1		88
#define	VECT_LVD2_LVD2		89
#define	VECT_USB0_USBR0		90
#define	VECT_RTC_ALM		92
#define	VECT_RTC_PRD		93
#define	VECT_IWDT_IWUNI		95
#define	VECT_WDT_WUNI		96
#define	VECT_PDC_PCDFI		97
#define	VECT_SCI7_RXI7		98
#define	VECT_SCI7_TXI7		99
#define	VECT_SCI8_RXI8		100
#define	VECT_SCI8_TXI8		101
#define	VECT_SCI9_RXI9		102
#define	VECT_SCI9_TXI9		103
#define	VECT_SCI10_RXI10	104
#define	VECT_SCI10_TXI10	105
#define	VECT_ICU_GROUPBE0	106
#define	VECT_ICU_GROUPBL2	107
#define	VECT_RSPI2_SPRI2	108
#define	VECT_RSPI2_SPTI2	109
#define	VECT_ICU_GROUPBL0	110
#define	VECT_ICU_GROUPBL1	111
#define	VECT_ICU_GROUPAL0	112
#define	VECT_ICU_GROUPAL1	113
#define	VECT_SCI11_RXI11	114
#define	VECT_SCI11_TXI11	115
#define	VECT_SCI12_RXI12	116
#define	VECT_SCI12_TXI12	117
#define	VECT_DMAC_DMAC0I	120
#define	VECT_DMAC_DMAC1I	121
#define	VECT_DMAC_DMAC2I	122
#define	VECT_DMAC_DMAC3I	123
#define	VECT_DMAC_DMAC74I	124
#define	VECT_OST_OSTDI		125
#define	VECT_EXDMAC_EXDMAC0I	126
#define	VECT_EXDMAC_EXDMAC1I	127
#define	VECT_PERIB_INTB128	128
#define	VECT_PERIB_INTB129	129
#define	VECT_PERIB_INTB130	130
#define	VECT_PERIB_INTB131	131
#define	VECT_PERIB_INTB132	132
#define	VECT_PERIB_INTB133	133
#define	VECT_PERIB_INTB134	134
#define	VECT_PERIB_INTB135	135
#define	VECT_PERIB_INTB136	136
#define	VECT_PERIB_INTB137	137
#define	VECT_PERIB_INTB138	138
#define	VECT_PERIB_INTB139	139
#define	VECT_PERIB_INTB140	140
#define	VECT_PERIB_INTB141	141
#define	VECT_PERIB_INTB142	142
#define	VECT_PERIB_INTB143	143
#define	VECT_PERIB_INTB144	144
#define	VECT_PERIB_INTB145	145
#define	VECT_PERIB_INTB146	146
#define	VECT_PERIB_INTB147	147
#define	VECT_PERIB_INTB148	148
#define	VECT_PERIB_INTB149	149
#define	VECT_PERIB_INTB150	150
#define	VECT_PERIB_INTB151	151
#define	VECT_PERIB_INTB152	152
#define	VECT_PERIB_INTB153	153
#define	VECT_PERIB_INTB154	154
#define	VECT_PERIB_INTB155	155
#define	VECT_PERIB_INTB156	156
#define	VECT_PERIB_INTB157	157
#define	VECT_PERIB_INTB158	158
#define	VECT_PERIB_INTB159	159
#define	VECT_PERIB_INTB160	160
#define	VECT_PERIB_INTB161	161
#define	VECT_PERIB_INTB162	162
#define	VECT_PERIB_INTB163	163
#define	VECT_PERIB_INTB164	164
#define	VECT_PERIB_INTB165	165
#define	VECT_PERIB_INTB166	166
#define	VECT_PERIB_INTB167	167
#define	VECT_PERIB_INTB168	168
#define	VECT_PERIB_INTB169	169
#define	VECT_PERIB_INTB170	170
#define	VECT_PERIB_INTB171	171
#define	VECT_PERIB_INTB172	172
#define	VECT_PERIB_INTB173	173
#define	VECT_PERIB_INTB174	174
#define	VECT_PERIB_INTB175	175
#define	VECT_PERIB_INTB176	176
#define	VECT_PERIB_INTB177	177
#define	VECT_PERIB_INTB178	178
#define	VECT_PERIB_INTB179	179
#define	VECT_PERIB_INTB180	180
#define	VECT_PERIB_INTB181	181
#define	VECT_PERIB_INTB182	182
#define	VECT_PERIB_INTB183	183
#define	VECT_PERIB_INTB184	184
#define	VECT_PERIB_INTB185	185
#define	VECT_PERIB_INTB186	186
#define	VECT_PERIB_INTB187	187
#define	VECT_PERIB_INTB188	188
#define	VECT_PERIB_INTB189	189
#define	VECT_PERIB_INTB190	190
#define	VECT_PERIB_INTB191	191
#define	VECT_PERIB_INTB192	192
#define	VECT_PERIB_INTB193	193
#define	VECT_PERIB_INTB194	194
#define	VECT_PERIB_INTB195	195
#define	VECT_PERIB_INTB196	196
#define	VECT_PERIB_INTB197	197
#define	VECT_PERIB_INTB198	198
#define	VECT_PERIB_INTB199	199
#define	VECT_PERIB_INTB200	200
#define	VECT_PERIB_INTB201	201
#define	VECT_PERIB_INTB202	202
#define	VECT_PERIB_INTB203	203
#define	VECT_PERIB_INTB204	204
#define	VECT_PERIB_INTB205	205
#define	VECT_PERIB_INTB206	206
#define	VECT_PERIB_INTB207	207
#define	VECT_PERIA_INTA208	208
#define	VECT_PERIA_INTA209	209
#define	VECT_PERIA_INTA210	210
#define	VECT_PERIA_INTA211	211
#define	VECT_PERIA_INTA212	212
#define	VECT_PERIA_INTA213	213
#define	VECT_PERIA_INTA214	214
#define	VECT_PERIA_INTA215	215
#define	VECT_PERIA_INTA216	216
#define	VECT_PERIA_INTA217	217
#define	VECT_PERIA_INTA218	218
#define	VECT_PERIA_INTA219	219
#define	VECT_PERIA_INTA220	220
#define	VECT_PERIA_INTA221	221
#define	VECT_PERIA_INTA222	222
#define	VECT_PERIA_INTA223	223
#define	VECT_PERIA_INTA224	224
#define	VECT_PERIA_INTA225	225
#define	VECT_PERIA_INTA226	226
#define	VECT_PERIA_INTA227	227
#define	VECT_PERIA_INTA228	228
#define	VECT_PERIA_INTA229	229
#define	VECT_PERIA_INTA230	230
#define	VECT_PERIA_INTA231	231
#define	VECT_PERIA_INTA232	232
#define	VECT_PERIA_INTA233	233
#define	VECT_PERIA_INTA234	234
#define	VECT_PERIA_INTA235	235
#define	VECT_PERIA_INTA236	236
#define	VECT_PERIA_INTA237	237
#define	VECT_PERIA_INTA238	238
#define	VECT_PERIA_INTA239	239
#define	VECT_PERIA_INTA240	240
#define	VECT_PERIA_INTA241	241
#define	VECT_PERIA_INTA242	242
#define	VECT_PERIA_INTA243	243
#define	VECT_PERIA_INTA244	244
#define	VECT_PERIA_INTA245	245
#define	VECT_PERIA_INTA246	246
#define	VECT_PERIA_INTA247	247
#define	VECT_PERIA_INTA248	248
#define	VECT_PERIA_INTA249	249
#define	VECT_PERIA_INTA250	250
#define	VECT_PERIA_INTA251	251
#define	VECT_PERIA_INTA252	252
#define	VECT_PERIA_INTA253	253
#define	VECT_PERIA_INTA254	254
#define	VECT_PERIA_INTA255	255

#define	MSTP_EXDMAC		SYSTEM.MSTPCRA.BIT.MSTPA29
#define	MSTP_EXDMAC0	SYSTEM.MSTPCRA.BIT.MSTPA29
#define	MSTP_EXDMAC1	SYSTEM.MSTPCRA.BIT.MSTPA29
#define	MSTP_DMAC		SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_DMAC0		SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_DMAC1		SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_DMAC2		SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_DMAC3		SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_DMAC4		SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_DMAC5		SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_DMAC6		SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_DMAC7		SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_DTC		SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_DA			SYSTEM.MSTPCRA.BIT.MSTPA19
#define	MSTP_S12AD		SYSTEM.MSTPCRA.BIT.MSTPA17
#define	MSTP_S12AD1		SYSTEM.MSTPCRA.BIT.MSTPA16
#define	MSTP_CMT0		SYSTEM.MSTPCRA.BIT.MSTPA15
#define	MSTP_CMT1		SYSTEM.MSTPCRA.BIT.MSTPA15
#define	MSTP_CMT2		SYSTEM.MSTPCRA.BIT.MSTPA14
#define	MSTP_CMT3		SYSTEM.MSTPCRA.BIT.MSTPA14
#define	MSTP_TPU0		SYSTEM.MSTPCRA.BIT.MSTPA13
#define	MSTP_TPU1		SYSTEM.MSTPCRA.BIT.MSTPA13
#define	MSTP_TPU2		SYSTEM.MSTPCRA.BIT.MSTPA13
#define	MSTP_TPU3		SYSTEM.MSTPCRA.BIT.MSTPA13
#define	MSTP_TPU4		SYSTEM.MSTPCRA.BIT.MSTPA13
#define	MSTP_TPU5		SYSTEM.MSTPCRA.BIT.MSTPA13
#define	MSTP_TPUA		SYSTEM.MSTPCRA.BIT.MSTPA13
#define	MSTP_PPG0		SYSTEM.MSTPCRA.BIT.MSTPA11
#define	MSTP_PPG1		SYSTEM.MSTPCRA.BIT.MSTPA10
#define	MSTP_MTU		SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU0		SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU1		SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU2		SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU3		SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU4		SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU5		SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU6		SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU7		SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU8		SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_GPTW		SYSTEM.MSTPCRA.BIT.MSTPA7
#define	MSTP_GPTW0		SYSTEM.MSTPCRA.BIT.MSTPA7
#define	MSTP_GPTW1		SYSTEM.MSTPCRA.BIT.MSTPA7
#define	MSTP_GPTW2		SYSTEM.MSTPCRA.BIT.MSTPA7
#define	MSTP_GPTW3		SYSTEM.MSTPCRA.BIT.MSTPA7
#define	MSTP_POEG		SYSTEM.MSTPCRA.BIT.MSTPA7
#define	MSTP_TMR0		SYSTEM.MSTPCRA.BIT.MSTPA5
#define	MSTP_TMR1		SYSTEM.MSTPCRA.BIT.MSTPA5
#define	MSTP_TMR01		SYSTEM.MSTPCRA.BIT.MSTPA5
#define	MSTP_TMR2		SYSTEM.MSTPCRA.BIT.MSTPA4
#define	MSTP_TMR3		SYSTEM.MSTPCRA.BIT.MSTPA4
#define	MSTP_TMR23		SYSTEM.MSTPCRA.BIT.MSTPA4
#define	MSTP_CMTW0		SYSTEM.MSTPCRA.BIT.MSTPA1
#define	MSTP_CMTW1		SYSTEM.MSTPCRA.BIT.MSTPA0
#define	MSTP_SCI0		SYSTEM.MSTPCRB.BIT.MSTPB31
#define	MSTP_SMCI0		SYSTEM.MSTPCRB.BIT.MSTPB31
#define	MSTP_SCI1		SYSTEM.MSTPCRB.BIT.MSTPB30
#define	MSTP_SMCI1		SYSTEM.MSTPCRB.BIT.MSTPB30
#define	MSTP_SCI2		SYSTEM.MSTPCRB.BIT.MSTPB29
#define	MSTP_SMCI2		SYSTEM.MSTPCRB.BIT.MSTPB29
#define	MSTP_SCI3		SYSTEM.MSTPCRB.BIT.MSTPB28
#define	MSTP_SMCI3		SYSTEM.MSTPCRB.BIT.MSTPB28
#define	MSTP_SCI4		SYSTEM.MSTPCRB.BIT.MSTPB27
#define	MSTP_SMCI4		SYSTEM.MSTPCRB.BIT.MSTPB27
#define	MSTP_SCI5		SYSTEM.MSTPCRB.BIT.MSTPB26
#define	MSTP_SMCI5		SYSTEM.MSTPCRB.BIT.MSTPB26
#define	MSTP_SCI6		SYSTEM.MSTPCRB.BIT.MSTPB25
#define	MSTP_SMCI6		SYSTEM.MSTPCRB.BIT.MSTPB25
#define	MSTP_SCI7		SYSTEM.MSTPCRB.BIT.MSTPB24
#define	MSTP_SMCI7		SYSTEM.MSTPCRB.BIT.MSTPB24
#define	MSTP_CRC		SYSTEM.MSTPCRB.BIT.MSTPB23
#define	MSTP_PDC		SYSTEM.MSTPCRB.BIT.MSTPB22
#define	MSTP_RIIC0		SYSTEM.MSTPCRB.BIT.MSTPB21
#define	MSTP_RIIC1		SYSTEM.MSTPCRB.BIT.MSTPB20
#define	MSTP_USB0		SYSTEM.MSTPCRB.BIT.MSTPB19
#define	MSTP_RSPI0		SYSTEM.MSTPCRB.BIT.MSTPB17
#define	MSTP_RSPI1		SYSTEM.MSTPCRB.BIT.MSTPB16
#define	MSTP_ETHERC0	SYSTEM.MSTPCRB.BIT.MSTPB15
#define	MSTP_EDMAC0		SYSTEM.MSTPCRB.BIT.MSTPB15
#define	MSTP_PMGI0		SYSTEM.MSTPCRB.BIT.MSTPB15
#define	MSTP_ETHERC1	SYSTEM.MSTPCRB.BIT.MSTPB14
#define	MSTP_EDMAC1		SYSTEM.MSTPCRB.BIT.MSTPB14
#define	MSTP_PMGI1		SYSTEM.MSTPCRB.BIT.MSTPB14
#define	MSTP_EPTPC		SYSTEM.MSTPCRB.BIT.MSTPB13
#define	MSTP_EPTPC0		SYSTEM.MSTPCRB.BIT.MSTPB13
#define	MSTP_EPTPC1		SYSTEM.MSTPCRB.BIT.MSTPB13
#define	MSTP_PTPEDMAC	SYSTEM.MSTPCRB.BIT.MSTPB13
#define	MSTP_ELC		SYSTEM.MSTPCRB.BIT.MSTPB9
#define	MSTP_TEMPS		SYSTEM.MSTPCRB.BIT.MSTPB8
#define	MSTP_DOC		SYSTEM.MSTPCRB.BIT.MSTPB6
#define	MSTP_SCI12		SYSTEM.MSTPCRB.BIT.MSTPB4
#define	MSTP_SMCI12		SYSTEM.MSTPCRB.BIT.MSTPB4
#define	MSTP_CAN2		SYSTEM.MSTPCRB.BIT.MSTPB2
#define	MSTP_CAN1		SYSTEM.MSTPCRB.BIT.MSTPB1
#define	MSTP_CAN0		SYSTEM.MSTPCRB.BIT.MSTPB0
#define	MSTP_GLCDC		SYSTEM.MSTPCRC.BIT.MSTPC29
#define	MSTP_DRW2D		SYSTEM.MSTPCRC.BIT.MSTPC28
#define	MSTP_SCI8		SYSTEM.MSTPCRC.BIT.MSTPC27
#define	MSTP_SMCI8		SYSTEM.MSTPCRC.BIT.MSTPC27
#define	MSTP_SCI9		SYSTEM.MSTPCRC.BIT.MSTPC26
#define	MSTP_SMCI9		SYSTEM.MSTPCRC.BIT.MSTPC26
#define	MSTP_SCI10		SYSTEM.MSTPCRC.BIT.MSTPC25
#define	MSTP_SMCI10		SYSTEM.MSTPCRC.BIT.MSTPC25
#define	MSTP_SCI11		SYSTEM.MSTPCRC.BIT.MSTPC24
#define	MSTP_SMCI11		SYSTEM.MSTPCRC.BIT.MSTPC24
#define	MSTP_QSPI		SYSTEM.MSTPCRC.BIT.MSTPC23
#define	MSTP_RSPI2		SYSTEM.MSTPCRC.BIT.MSTPC22
#define	MSTP_CAC		SYSTEM.MSTPCRC.BIT.MSTPC19
#define	MSTP_RIIC2		SYSTEM.MSTPCRC.BIT.MSTPC17
#define	MSTP_STBYRAM	SYSTEM.MSTPCRC.BIT.MSTPC7
#define	MSTP_ECCRAM		SYSTEM.MSTPCRC.BIT.MSTPC6
#define	MSTP_RAM2		SYSTEM.MSTPCRC.BIT.MSTPC2
#define	MSTP_RAM0		SYSTEM.MSTPCRC.BIT.MSTPC0
#define	MSTP_TSIP		SYSTEM.MSTPCRD.BIT.MSTPD27
#define	MSTP_MMCIF		SYSTEM.MSTPCRD.BIT.MSTPD21
#define	MSTP_SDHI		SYSTEM.MSTPCRD.BIT.MSTPD19
#define	MSTP_SSIE0		SYSTEM.MSTPCRD.BIT.MSTPD15
#define	MSTP_SSIE1		SYSTEM.MSTPCRD.BIT.MSTPD14

#define	IS_DPFPU_DPFPUEX		IS0
#define	IS_CAN0_ERS0			IS0
#define	IS_CAN1_ERS1			IS1
#define	IS_CAN2_ERS2			IS2
#define	IS_SCI0_TEI0			IS0
#define	IS_SCI0_ERI0			IS1
#define	IS_SCI1_TEI1			IS2
#define	IS_SCI1_ERI1			IS3
#define	IS_SCI2_TEI2			IS4
#define	IS_SCI2_ERI2			IS5
#define	IS_SCI3_TEI3			IS6
#define	IS_SCI3_ERI3			IS7
#define	IS_SCI4_TEI4			IS8
#define	IS_SCI4_ERI4			IS9
#define	IS_SCI5_TEI5			IS10
#define	IS_SCI5_ERI5			IS11
#define	IS_SCI6_TEI6			IS12
#define	IS_SCI6_ERI6			IS13
#define	IS_SCI12_TEI12			IS16
#define	IS_SCI12_ERI12			IS17
#define	IS_SCI12_SCIX0			IS18
#define	IS_SCI12_SCIX1			IS19
#define	IS_SCI12_SCIX2			IS20
#define	IS_SCI12_SCIX3			IS21
#define	IS_QSPI_QSPSSLI			IS24
#define	IS_CAC_FERRI			IS26
#define	IS_CAC_MENDI			IS27
#define	IS_CAC_OVFI				IS28
#define	IS_DOC_DOPCI			IS29
#define	IS_PDC_PCFEI			IS30
#define	IS_PDC_PCERI			IS31
#define	IS_SDHI_CDETI			IS3
#define	IS_SDHI_CACI			IS4
#define	IS_SDHI_SDACI			IS5
#define	IS_MMCIF_CDETIO			IS6
#define	IS_MMCIF_ERRIO			IS7
#define	IS_MMCIF_ACCIO			IS8
#define	IS_POE3_OEI1			IS9
#define	IS_POE3_OEI2			IS10
#define	IS_POE3_OEI3			IS11
#define	IS_POE3_OEI4			IS12
#define	IS_RIIC0_TEI0			IS13
#define	IS_RIIC0_EEI0			IS14
#define	IS_RIIC2_TEI2			IS15
#define	IS_RIIC2_EEI2			IS16
#define	IS_SSIE0_SSIF0			IS17
#define	IS_SSIE1_SSIF1			IS18
#define	IS_S12AD_S12CMPAI		IS20
#define	IS_S12AD_S12CMPBI		IS21
#define	IS_S12AD1_S12CMPAI1		IS22
#define	IS_S12AD1_S12CMPBI1		IS23
#define	IS_RIIC1_TEI1			IS28
#define	IS_RIIC1_EEI1			IS29
#define	IS_POEG_POEGGAI			IS7
#define	IS_POEG_POEGGBI			IS8
#define	IS_POEG_POEGGCI			IS9
#define	IS_POEG_POEGGDI			IS10
#define	IS_SCI8_TEI8			IS0
#define	IS_SCI8_ERI8			IS1
#define	IS_SCI9_TEI9			IS4
#define	IS_SCI9_ERI9			IS5
#define	IS_SCI10_TEI10			IS8
#define	IS_SCI10_ERI10			IS9
#define	IS_SCI11_TEI11			IS12
#define	IS_SCI11_ERI11			IS13
#define	IS_RSPI0_SPII0			IS16
#define	IS_RSPI0_SPEI0			IS17
#define	IS_RSPI1_SPII1			IS18
#define	IS_RSPI1_SPEI1			IS19
#define	IS_RSPI2_SPII2			IS20
#define	IS_RSPI2_SPEI2			IS21
#define	IS_SCI7_TEI7			IS22
#define	IS_SCI7_ERI7			IS23
#define	IS_EPTPC_MINT			IS0
#define	IS_PTPEDMAC_PINT		IS1
#define	IS_EDMAC0_EINT0			IS4
#define	IS_EDMAC1_EINT1			IS5
#define	IS_GLCDC_VPOS			IS8
#define	IS_GLCDC_GR1UF			IS9
#define	IS_GLCDC_GR2UF			IS10
#define	IS_DRW2D_DRWIRQ			IS11

#define	EN_DPFPU_DPFPUEX		EN0
#define	EN_CAN0_ERS0			EN0
#define	EN_CAN1_ERS1			EN1
#define	EN_CAN2_ERS2			EN2
#define	EN_SCI0_TEI0			EN0
#define	EN_SCI0_ERI0			EN1
#define	EN_SCI1_TEI1			EN2
#define	EN_SCI1_ERI1			EN3
#define	EN_SCI2_TEI2			EN4
#define	EN_SCI2_ERI2			EN5
#define	EN_SCI3_TEI3			EN6
#define	EN_SCI3_ERI3			EN7
#define	EN_SCI4_TEI4			EN8
#define	EN_SCI4_ERI4			EN9
#define	EN_SCI5_TEI5			EN10
#define	EN_SCI5_ERI5			EN11
#define	EN_SCI6_TEI6			EN12
#define	EN_SCI6_ERI6			EN13
#define	EN_SCI12_TEI12			EN16
#define	EN_SCI12_ERI12			EN17
#define	EN_SCI12_SCIX0			EN18
#define	EN_SCI12_SCIX1			EN19
#define	EN_SCI12_SCIX2			EN20
#define	EN_SCI12_SCIX3			EN21
#define	EN_QSPI_QSPSSLI			EN24
#define	EN_CAC_FERRI			EN26
#define	EN_CAC_MENDI			EN27
#define	EN_CAC_OVFI				EN28
#define	EN_DOC_DOPCI			EN29
#define	EN_PDC_PCFEI			EN30
#define	EN_PDC_PCERI			EN31
#define	EN_SDHI_CDETI			EN3
#define	EN_SDHI_CACI			EN4
#define	EN_SDHI_SDACI			EN5
#define	EN_MMCIF_CDETIO			EN6
#define	EN_MMCIF_ERRIO			EN7
#define	EN_MMCIF_ACCIO			EN8
#define	EN_POE3_OEI1			EN9
#define	EN_POE3_OEI2			EN10
#define	EN_POE3_OEI3			EN11
#define	EN_POE3_OEI4			EN12
#define	EN_RIIC0_TEI0			EN13
#define	EN_RIIC0_EEI0			EN14
#define	EN_RIIC2_TEI2			EN15
#define	EN_RIIC2_EEI2			EN16
#define	EN_SSIE0_SSIF0			EN17
#define	EN_SSIE1_SSIF1			EN18
#define	EN_S12AD_S12CMPAI		EN20
#define	EN_S12AD_S12CMPBI		EN21
#define	EN_S12AD1_S12CMPAI1		EN22
#define	EN_S12AD1_S12CMPBI1		EN23
#define	EN_RIIC1_TEI1			EN28
#define	EN_RIIC1_EEI1			EN29
#define	EN_POEG_POEGGAI			EN7
#define	EN_POEG_POEGGBI			EN8
#define	EN_POEG_POEGGCI			EN9
#define	EN_POEG_POEGGDI			EN10
#define	EN_SCI8_TEI8			EN0
#define	EN_SCI8_ERI8			EN1
#define	EN_SCI9_TEI9			EN4
#define	EN_SCI9_ERI9			EN5
#define	EN_SCI10_TEI10			EN8
#define	EN_SCI10_ERI10			EN9
#define	EN_SCI11_TEI11			EN12
#define	EN_SCI11_ERI11			EN13
#define	EN_RSPI0_SPII0			EN16
#define	EN_RSPI0_SPEI0			EN17
#define	EN_RSPI1_SPII1			EN18
#define	EN_RSPI1_SPEI1			EN19
#define	EN_RSPI2_SPII2			EN20
#define	EN_RSPI2_SPEI2			EN21
#define	EN_SCI7_TEI7			EN22
#define	EN_SCI7_ERI7			EN23
#define	EN_EPTPC_MINT			EN0
#define	EN_PTPEDMAC_PINT		EN1
#define	EN_EDMAC0_EINT0			EN4
#define	EN_EDMAC1_EINT1			EN5
#define	EN_GLCDC_VPOS			EN8
#define	EN_GLCDC_GR1UF			EN9
#define	EN_GLCDC_GR2UF			EN10
#define	EN_DRW2D_DRWIRQ			EN11

#define	CLR_DPFPU_DPFPUEX		CLR0
#define	CLR_CAN0_ERS0			CLR0
#define	CLR_CAN1_ERS1			CLR1
#define	CLR_CAN2_ERS2			CLR2

#define	GEN_DPFPU_DPFPUEX		GENIE0
#define	GEN_CAN0_ERS0			GENBE0
#define	GEN_CAN1_ERS1			GENBE0
#define	GEN_CAN2_ERS2			GENBE0
#define	GEN_SCI0_TEI0			GENBL0
#define	GEN_SCI0_ERI0			GENBL0
#define	GEN_SCI1_TEI1			GENBL0
#define	GEN_SCI1_ERI1			GENBL0
#define	GEN_SCI2_TEI2			GENBL0
#define	GEN_SCI2_ERI2			GENBL0
#define	GEN_SCI3_TEI3			GENBL0
#define	GEN_SCI3_ERI3			GENBL0
#define	GEN_SCI4_TEI4			GENBL0
#define	GEN_SCI4_ERI4			GENBL0
#define	GEN_SCI5_TEI5			GENBL0
#define	GEN_SCI5_ERI5			GENBL0
#define	GEN_SCI6_TEI6			GENBL0
#define	GEN_SCI6_ERI6			GENBL0
#define	GEN_SCI12_TEI12			GENBL0
#define	GEN_SCI12_ERI12			GENBL0
#define	GEN_SCI12_SCIX0			GENBL0
#define	GEN_SCI12_SCIX1			GENBL0
#define	GEN_SCI12_SCIX2			GENBL0
#define	GEN_SCI12_SCIX3			GENBL0
#define	GEN_QSPI_QSPSSLI		GENBL0
#define	GEN_CAC_FERRI			GENBL0
#define	GEN_CAC_MENDI			GENBL0
#define	GEN_CAC_OVFI			GENBL0
#define	GEN_DOC_DOPCI			GENBL0
#define	GEN_PDC_PCFEI			GENBL0
#define	GEN_PDC_PCERI			GENBL0
#define	GEN_SDHI_CDETI			GENBL1
#define	GEN_SDHI_CACI			GENBL1
#define	GEN_SDHI_SDACI			GENBL1
#define	GEN_MMCIF_CDETIO		GENBL1
#define	GEN_MMCIF_ERRIO			GENBL1
#define	GEN_MMCIF_ACCIO			GENBL1
#define	GEN_POE3_OEI1			GENBL1
#define	GEN_POE3_OEI2			GENBL1
#define	GEN_POE3_OEI3			GENBL1
#define	GEN_POE3_OEI4			GENBL1
#define	GEN_RIIC0_TEI0			GENBL1
#define	GEN_RIIC0_EEI0			GENBL1
#define	GEN_RIIC2_TEI2			GENBL1
#define	GEN_RIIC2_EEI2			GENBL1
#define	GEN_SSIE0_SSIF0			GENBL1
#define	GEN_SSIE1_SSIF1			GENBL1
#define	GEN_S12AD_S12CMPAI		GENBL1
#define	GEN_S12AD_S12CMPBI		GENBL1
#define	GEN_S12AD1_S12CMPAI1	GENBL1
#define	GEN_S12AD1_S12CMPBI1	GENBL1
#define	GEN_RIIC1_TEI1			GENBL1
#define	GEN_RIIC1_EEI1			GENBL1
#define	GEN_POEG_POEGGAI		GENBL2
#define	GEN_POEG_POEGGBI		GENBL2
#define	GEN_POEG_POEGGCI		GENBL2
#define	GEN_POEG_POEGGDI		GENBL2
#define	GEN_SCI8_TEI8			GENAL0
#define	GEN_SCI8_ERI8			GENAL0
#define	GEN_SCI9_TEI9			GENAL0
#define	GEN_SCI9_ERI9			GENAL0
#define	GEN_SCI10_TEI10			GENAL0
#define	GEN_SCI10_ERI10			GENAL0
#define	GEN_SCI11_TEI11			GENAL0
#define	GEN_SCI11_ERI11			GENAL0
#define	GEN_RSPI0_SPII0			GENAL0
#define	GEN_RSPI0_SPEI0			GENAL0
#define	GEN_RSPI1_SPII1			GENAL0
#define	GEN_RSPI1_SPEI1			GENAL0
#define	GEN_RSPI2_SPII2			GENAL0
#define	GEN_RSPI2_SPEI2			GENAL0
#define	GEN_SCI7_TEI7			GENAL0
#define	GEN_SCI7_ERI7			GENAL0
#define	GEN_EPTPC_MINT			GENAL1
#define	GEN_PTPEDMAC_PINT		GENAL1
#define	GEN_EDMAC0_EINT0		GENAL1
#define	GEN_EDMAC1_EINT1		GENAL1
#define	GEN_GLCDC_VPOS			GENAL1
#define	GEN_GLCDC_GR1UF			GENAL1
#define	GEN_GLCDC_GR2UF			GENAL1
#define	GEN_DRW2D_DRWIRQ		GENAL1

#define	GRP_DPFPU_DPFPUEX		GRPIE0
#define	GRP_CAN0_ERS0			GRPBE0
#define	GRP_CAN1_ERS1			GRPBE0
#define	GRP_CAN2_ERS2			GRPBE0
#define	GRP_SCI0_TEI0			GRPBL0
#define	GRP_SCI0_ERI0			GRPBL0
#define	GRP_SCI1_TEI1			GRPBL0
#define	GRP_SCI1_ERI1			GRPBL0
#define	GRP_SCI2_TEI2			GRPBL0
#define	GRP_SCI2_ERI2			GRPBL0
#define	GRP_SCI3_TEI3			GRPBL0
#define	GRP_SCI3_ERI3			GRPBL0
#define	GRP_SCI4_TEI4			GRPBL0
#define	GRP_SCI4_ERI4			GRPBL0
#define	GRP_SCI5_TEI5			GRPBL0
#define	GRP_SCI5_ERI5			GRPBL0
#define	GRP_SCI6_TEI6			GRPBL0
#define	GRP_SCI6_ERI6			GRPBL0
#define	GRP_SCI12_TEI12			GRPBL0
#define	GRP_SCI12_ERI12			GRPBL0
#define	GRP_SCI12_SCIX0			GRPBL0
#define	GRP_SCI12_SCIX1			GRPBL0
#define	GRP_SCI12_SCIX2			GRPBL0
#define	GRP_SCI12_SCIX3			GRPBL0
#define	GRP_QSPI_QSPSSLI		GRPBL0
#define	GRP_CAC_FERRI			GRPBL0
#define	GRP_CAC_MENDI			GRPBL0
#define	GRP_CAC_OVFI			GRPBL0
#define	GRP_DOC_DOPCI			GRPBL0
#define	GRP_PDC_PCFEI			GRPBL0
#define	GRP_PDC_PCERI			GRPBL0
#define	GRP_SDHI_CDETI			GRPBL1
#define	GRP_SDHI_CACI			GRPBL1
#define	GRP_SDHI_SDACI			GRPBL1
#define	GRP_MMCIF_CDETIO		GRPBL1
#define	GRP_MMCIF_ERRIO			GRPBL1
#define	GRP_MMCIF_ACCIO			GRPBL1
#define	GRP_POE3_OEI1			GRPBL1
#define	GRP_POE3_OEI2			GRPBL1
#define	GRP_POE3_OEI3			GRPBL1
#define	GRP_POE3_OEI4			GRPBL1
#define	GRP_RIIC0_TEI0			GRPBL1
#define	GRP_RIIC0_EEI0			GRPBL1
#define	GRP_RIIC2_TEI2			GRPBL1
#define	GRP_RIIC2_EEI2			GRPBL1
#define	GRP_SSIE0_SSIF0			GRPBL1
#define	GRP_SSIE1_SSIF1			GRPBL1
#define	GRP_S12AD_S12CMPAI		GRPBL1
#define	GRP_S12AD_S12CMPBI		GRPBL1
#define	GRP_S12AD1_S12CMPAI1	GRPBL1
#define	GRP_S12AD1_S12CMPBI1	GRPBL1
#define	GRP_RIIC1_TEI1			GRPBL1
#define	GRP_RIIC1_EEI1			GRPBL1
#define	GRP_POEG_POEGGAI		GRPBL2
#define	GRP_POEG_POEGGBI		GRPBL2
#define	GRP_POEG_POEGGCI		GRPBL2
#define	GRP_POEG_POEGGDI		GRPBL2
#define	GRP_SCI8_TEI8			GRPAL0
#define	GRP_SCI8_ERI8			GRPAL0
#define	GRP_SCI9_TEI9			GRPAL0
#define	GRP_SCI9_ERI9			GRPAL0
#define	GRP_SCI10_TEI10			GRPAL0
#define	GRP_SCI10_ERI10			GRPAL0
#define	GRP_SCI11_TEI11			GRPAL0
#define	GRP_SCI11_ERI11			GRPAL0
#define	GRP_RSPI0_SPII0			GRPAL0
#define	GRP_RSPI0_SPEI0			GRPAL0
#define	GRP_RSPI1_SPII1			GRPAL0
#define	GRP_RSPI1_SPEI1			GRPAL0
#define	GRP_RSPI2_SPII2			GRPAL0
#define	GRP_RSPI2_SPEI2			GRPAL0
#define	GRP_SCI7_TEI7			GRPAL0
#define	GRP_SCI7_ERI7			GRPAL0
#define	GRP_EPTPC_MINT			GRPAL1
#define	GRP_PTPEDMAC_PINT		GRPAL1
#define	GRP_EDMAC0_EINT0		GRPAL1
#define	GRP_EDMAC1_EINT1		GRPAL1
#define	GRP_GLCDC_VPOS			GRPAL1
#define	GRP_GLCDC_GR1UF			GRPAL1
#define	GRP_GLCDC_GR2UF			GRPAL1
#define	GRP_DRW2D_DRWIRQ		GRPAL1

#define	GCR_DPFPU_DPFPUEX		GCRIE0
#define	GCR_CAN0_ERS0			GCRBE0
#define	GCR_CAN1_ERS1			GCRBE0
#define	GCR_CAN2_ERS2			GCRBE0

#define	__IR( x )		ICU.IR[ IR ## x ].BIT.IR
#define	 _IR( x )		__IR( x )
#define	  IR( x , y )	_IR( _ ## x ## _ ## y )
#define	__DTCE( x )		ICU.DTCER[ DTCE ## x ].BIT.DTCE
#define	 _DTCE( x )		__DTCE( x )
#define	  DTCE( x , y )	_DTCE( _ ## x ## _ ## y )
#define	__IEN( x )		ICU.IER[ IER ## x ].BIT.IEN ## x
#define	 _IEN( x )		__IEN( x )
#define	  IEN( x , y )	_IEN( _ ## x ## _ ## y )
#define	__IPR( x )		ICU.IPR[ IPR ## x ].BIT.IPR
#define	 _IPR( x )		__IPR( x )
#define	  IPR( x , y )	_IPR( _ ## x ## _ ## y )
#define	__VECT( x )		VECT ## x
#define	 _VECT( x )		__VECT( x )
#define	  VECT( x , y )	_VECT( _ ## x ## _ ## y )
#define	__MSTP( x )		MSTP ## x
#define	 _MSTP( x )		__MSTP( x )
#define	  MSTP( x )		_MSTP( _ ## x )

#define	__IS( x )		ICU.GRP ## x.BIT.IS ## x
#define	 _IS( x )		__IS( x )
#define	  IS( x , y )	_IS( _ ## x ## _ ## y )
#define	__EN( x )		ICU.GEN ## x.BIT.EN ## x
#define	 _EN( x )		__EN( x )
#define	  EN( x , y )	_EN( _ ## x ## _ ## y )
#define	__CLR( x )		ICU.GCR ## x.BIT.CLR ## x
#define	 _CLR( x )		__CLR( x )
#define	  CLR( x , y )	_CLR( _ ## x ## _ ## y )

#define	BSC			(*(volatile struct st_bsc       *)0x81300)
#define	CAC			(*(volatile struct st_cac       *)0x8B000)
#define	CAN0		(*(volatile struct st_can       *)0x90200)
#define	CAN1		(*(volatile struct st_can       *)0x91200)
#define	CAN2		(*(volatile struct st_can       *)0x92200)
#define	CMT			(*(volatile struct st_cmt       *)0x88000)
#define	CMT0		(*(volatile struct st_cmt0      *)0x88002)
#define	CMT1		(*(volatile struct st_cmt0      *)0x88008)
#define	CMT2		(*(volatile struct st_cmt0      *)0x88012)
#define	CMT3		(*(volatile struct st_cmt0      *)0x88018)
#define	CMTW0		(*(volatile struct st_cmtw      *)0x94200)
#define	CMTW1		(*(volatile struct st_cmtw      *)0x94280)
#define	CRC			(*(volatile struct st_crc       *)0x88280)
#define	DA			(*(volatile struct st_da        *)0x88040)
#define	DMAC		(*(volatile struct st_dmac      *)0x82200)
#define	DMAC0		(*(volatile struct st_dmac0     *)0x82000)
#define	DMAC1		(*(volatile struct st_dmac1     *)0x82040)
#define	DMAC2		(*(volatile struct st_dmac1     *)0x82080)
#define	DMAC3		(*(volatile struct st_dmac1     *)0x820C0)
#define	DMAC4		(*(volatile struct st_dmac1     *)0x82100)
#define	DMAC5		(*(volatile struct st_dmac1     *)0x82140)
#define	DMAC6		(*(volatile struct st_dmac1     *)0x82180)
#define	DMAC7		(*(volatile struct st_dmac1     *)0x821C0)
#define	DOC			(*(volatile struct st_doc       *)0x8B080)
#define	DRW2D		(*(volatile struct st_drw2d     *)0xE3000)
#define	DTC			(*(volatile struct st_dtc       *)0x82400)
#define	ECCRAM		(*(volatile struct st_eccram    *)0x812C0)
#define	EDMAC0		(*(volatile struct st_edmac     *)0xC0000)
#define	EDMAC1		(*(volatile struct st_edmac     *)0xC0200)
#define	ELC			(*(volatile struct st_elc       *)0x8B100)
#define	EPTPC		(*(volatile struct st_eptpc     *)0xC0500)
#define	EPTPC0		(*(volatile struct st_eptpc0    *)0xC4800)
#define	EPTPC1		(*(volatile struct st_eptpc0    *)0xC4C00)
#define	ETHERC0		(*(volatile struct st_etherc    *)0xC0100)
#define	ETHERC1		(*(volatile struct st_etherc    *)0xC0300)
#define	EXDMAC		(*(volatile struct st_exdmac    *)0x82A00)
#define	EXDMAC0		(*(volatile struct st_exdmac0   *)0x82800)
#define	EXDMAC1		(*(volatile struct st_exdmac1   *)0x82840)
#define	FLASH		(*(volatile struct st_flash     *)0x81000)
#define	GLCDC		(*(volatile struct st_glcdc     *)0xE0000)
#define	GPTW0		(*(volatile struct st_gptw      *)0xC2000)
#define	GPTW1		(*(volatile struct st_gptw      *)0xC2100)
#define	GPTW2		(*(volatile struct st_gptw      *)0xC2200)
#define	GPTW3		(*(volatile struct st_gptw      *)0xC2300)
#define	ICU			(*(volatile struct st_icu       *)0x87000)
#define	IWDT		(*(volatile struct st_iwdt      *)0x88030)
#define	MMCIF		(*(volatile struct st_mmcif     *)0x88500)
#define	MPC			(*(volatile struct st_mpc       *)0x8C100)
#define	MPU			(*(volatile struct st_mpu       *)0x86400)
#define	MTU			(*(volatile struct st_mtu       *)0xC120A)
#define	MTU0		(*(volatile struct st_mtu0      *)0xC1290)
#define	MTU1		(*(volatile struct st_mtu1      *)0xC1290)
#define	MTU2		(*(volatile struct st_mtu2      *)0xC1292)
#define	MTU3		(*(volatile struct st_mtu3      *)0xC1200)
#define	MTU4		(*(volatile struct st_mtu4      *)0xC1200)
#define	MTU5		(*(volatile struct st_mtu5      *)0xC1A94)
#define	MTU6		(*(volatile struct st_mtu6      *)0xC1A00)
#define	MTU7		(*(volatile struct st_mtu7      *)0xC1A00)
#define	MTU8		(*(volatile struct st_mtu8      *)0xC1298)
#define	OFSM		(*(volatile struct st_ofsm      *)0xFE7F5D00)
#define	PDC			(*(volatile struct st_pdc       *)0xA0500)
#define	PMGI0		(*(volatile struct st_pmgi      *)0xC5880)
#define	PMGI1		(*(volatile struct st_pmgi      *)0xC5890)
#define	POE3		(*(volatile struct st_poe       *)0x8C4C0)
#define	POEG		(*(volatile struct st_poeg      *)0x9E000)
#define	PORT0		(*(volatile struct st_port0     *)0x8C000)
#define	PORT1		(*(volatile struct st_port1     *)0x8C001)
#define	PORT2		(*(volatile struct st_port2     *)0x8C002)
#define	PORT3		(*(volatile struct st_port3     *)0x8C003)
#define	PORT4		(*(volatile struct st_port4     *)0x8C004)
#define	PORT5		(*(volatile struct st_port5     *)0x8C005)
#define	PORT6		(*(volatile struct st_port6     *)0x8C006)
#define	PORT7		(*(volatile struct st_port7     *)0x8C007)
#define	PORT8		(*(volatile struct st_port8     *)0x8C008)
#define	PORT9		(*(volatile struct st_port9     *)0x8C009)
#define	PORTA		(*(volatile struct st_porta     *)0x8C00A)
#define	PORTB		(*(volatile struct st_portb     *)0x8C00B)
#define	PORTC		(*(volatile struct st_portc     *)0x8C00C)
#define	PORTD		(*(volatile struct st_portd     *)0x8C00D)
#define	PORTE		(*(volatile struct st_porte     *)0x8C00E)
#define	PORTF		(*(volatile struct st_portf     *)0x8C00F)
#define	PORTG		(*(volatile struct st_portg     *)0x8C010)
#define	PORTH		(*(volatile struct st_porth     *)0x8C011)
#define	PORTJ		(*(volatile struct st_portj     *)0x8C012)
#define	PORTK		(*(volatile struct st_portk     *)0x8C013)
#define	PORTL		(*(volatile struct st_portl     *)0x8C014)
#define	PORTM		(*(volatile struct st_portm     *)0x8C015)
#define	PORTN		(*(volatile struct st_portn     *)0x8C016)
#define	PORTQ		(*(volatile struct st_portq     *)0x8C017)
#define	PPG0		(*(volatile struct st_ppg0      *)0x881E6)
#define	PPG1		(*(volatile struct st_ppg1      *)0x881F0)
#define	PTPEDMAC	(*(volatile struct st_ptpedmac  *)0xC0400)
#define	QSPI		(*(volatile struct st_qspi      *)0x89E00)
#define	RAM			(*(volatile struct st_ram       *)0x81200)
#define	RIIC0		(*(volatile struct st_riic      *)0x88300)
#define	RIIC1		(*(volatile struct st_riic      *)0x88320)
#define	RIIC2		(*(volatile struct st_riic      *)0x88340)
#define	RSPI0		(*(volatile struct st_rspi      *)0xD0100)
#define	RSPI1		(*(volatile struct st_rspi      *)0xD0140)
#define	RSPI2		(*(volatile struct st_rspi      *)0xD0300)
#define	RTC			(*(volatile struct st_rtc       *)0x8C400)
#define	S12AD		(*(volatile struct st_s12ad     *)0x89000)
#define	S12AD1		(*(volatile struct st_s12ad1    *)0x89100)
#define	SCI0		(*(volatile struct st_sci0      *)0x8A000)
#define	SCI1		(*(volatile struct st_sci0      *)0x8A020)
#define	SCI2		(*(volatile struct st_sci0      *)0x8A040)
#define	SCI3		(*(volatile struct st_sci0      *)0x8A060)
#define	SCI4		(*(volatile struct st_sci0      *)0x8A080)
#define	SCI5		(*(volatile struct st_sci0      *)0x8A0A0)
#define	SCI6		(*(volatile struct st_sci0      *)0x8A0C0)
#define	SCI7		(*(volatile struct st_sci7      *)0xD00E0)
#define	SCI8		(*(volatile struct st_sci7      *)0xD0000)
#define	SCI9		(*(volatile struct st_sci7      *)0xD0020)
#define	SCI10		(*(volatile struct st_sci7      *)0xD0040)
#define	SCI11		(*(volatile struct st_sci7      *)0xD0060)
#define	SCI12		(*(volatile struct st_sci12     *)0x8B300)
#define	SDHI		(*(volatile struct st_sdhi      *)0x8AC00)
#define	SMCI0		(*(volatile struct st_smci      *)0x8A000)
#define	SMCI1		(*(volatile struct st_smci      *)0x8A020)
#define	SMCI2		(*(volatile struct st_smci      *)0x8A040)
#define	SMCI3		(*(volatile struct st_smci      *)0x8A060)
#define	SMCI4		(*(volatile struct st_smci      *)0x8A080)
#define	SMCI5		(*(volatile struct st_smci      *)0x8A0A0)
#define	SMCI6		(*(volatile struct st_smci      *)0x8A0C0)
#define	SMCI7		(*(volatile struct st_smci      *)0xD00E0)
#define	SMCI8		(*(volatile struct st_smci      *)0xD0000)
#define	SMCI9		(*(volatile struct st_smci      *)0xD0020)
#define	SMCI10		(*(volatile struct st_smci      *)0xD0040)
#define	SMCI11		(*(volatile struct st_smci      *)0xD0060)
#define	SMCI12		(*(volatile struct st_smci      *)0x8B300)
#define	SSIE0		(*(volatile struct st_ssie      *)0x8A500)
#define	SSIE1		(*(volatile struct st_ssie      *)0x8A540)
#define	SYSTEM		(*(volatile struct st_system    *)0x80000)
#define	TEMPS		(*(volatile struct st_temps     *)0x8C500)
#define	TMR0		(*(volatile struct st_tmr0      *)0x88200)
#define	TMR1		(*(volatile struct st_tmr1      *)0x88201)
#define	TMR2		(*(volatile struct st_tmr0      *)0x88210)
#define	TMR3		(*(volatile struct st_tmr1      *)0x88211)
#define	TMR01		(*(volatile struct st_tmr01     *)0x88204)
#define	TMR23		(*(volatile struct st_tmr01     *)0x88214)
#define	TPU0		(*(volatile struct st_tpu0      *)0x88108)
#define	TPU1		(*(volatile struct st_tpu1      *)0x88108)
#define	TPU2		(*(volatile struct st_tpu2      *)0x8810A)
#define	TPU3		(*(volatile struct st_tpu3      *)0x8810A)
#define	TPU4		(*(volatile struct st_tpu4      *)0x8810C)
#define	TPU5		(*(volatile struct st_tpu5      *)0x8810C)
#define	TPUA		(*(volatile struct st_tpua      *)0x88100)
#define	USB			(*(volatile struct st_usb       *)0xA0400)
#define	USB0		(*(volatile struct st_usb0      *)0xA0000)
#define	WDT			(*(volatile struct st_wdt       *)0x88020)
#define	FLASHCONST	(*(volatile struct st_flashconst  *)0xFE7F7D90)
#define	TEMPSCONST	(*(volatile struct st_tempsconst  *)0xFE7F7D7C)

typedef enum enum_ir {
IR_BSC_BUSERR=16,IR_ICU_GROUPIE0=17,
IR_RAM_RAMERR,
IR_FCU_FIFERR=21,IR_FCU_FRDYI=23,
IR_ICU_SWINT2=26,IR_ICU_SWINT,
IR_CMT0_CMI0,
IR_CMT1_CMI1,
IR_CMTW0_CMWI0,
IR_CMTW1_CMWI1,
IR_USB0_D0FIFO0=34,IR_USB0_D1FIFO0,
IR_RSPI0_SPRI0=38,IR_RSPI0_SPTI0,
IR_RSPI1_SPRI1,IR_RSPI1_SPTI1,
IR_QSPI_SPRI,IR_QSPI_SPTI,
IR_SDHI_SBFAI,
IR_MMCIF_MBFAI,
IR_SSIE0_SSITXI0,IR_SSIE0_SSIRXI0,
IR_SSIE1_SSIRTI1,
IR_RIIC1_RXI1=50,IR_RIIC1_TXI1,
IR_RIIC0_RXI0,IR_RIIC0_TXI0,
IR_RIIC2_RXI2,IR_RIIC2_TXI2,
IR_SCI0_RXI0=58,IR_SCI0_TXI0,
IR_SCI1_RXI1,IR_SCI1_TXI1,
IR_SCI2_RXI2,IR_SCI2_TXI2,
IR_ICU_IRQ0,IR_ICU_IRQ1,IR_ICU_IRQ2,IR_ICU_IRQ3,IR_ICU_IRQ4,IR_ICU_IRQ5,IR_ICU_IRQ6,IR_ICU_IRQ7,
IR_ICU_IRQ8,IR_ICU_IRQ9,IR_ICU_IRQ10,IR_ICU_IRQ11,IR_ICU_IRQ12,IR_ICU_IRQ13,IR_ICU_IRQ14,IR_ICU_IRQ15,
IR_SCI3_RXI3,IR_SCI3_TXI3,
IR_SCI4_RXI4,IR_SCI4_TXI4,
IR_SCI5_RXI5,IR_SCI5_TXI5,
IR_SCI6_RXI6,IR_SCI6_TXI6,
IR_LVD1_LVD1,
IR_LVD2_LVD2,
IR_USB0_USBR0,
IR_RTC_ALM=92,IR_RTC_PRD,
IR_IWDT_IWUNI=95,
IR_WDT_WUNI,
IR_PDC_PCDFI,
IR_SCI7_RXI7,IR_SCI7_TXI7,
IR_SCI8_RXI8,IR_SCI8_TXI8,
IR_SCI9_RXI9,IR_SCI9_TXI9,
IR_SCI10_RXI10,IR_SCI10_TXI10,
IR_ICU_GROUPBE0,IR_ICU_GROUPBL2,
IR_RSPI2_SPRI2,IR_RSPI2_SPTI2,
IR_ICU_GROUPBL0,IR_ICU_GROUPBL1,IR_ICU_GROUPAL0,IR_ICU_GROUPAL1,
IR_SCI11_RXI11,IR_SCI11_TXI11,
IR_SCI12_RXI12,IR_SCI12_TXI12,
IR_DMAC_DMAC0I=120,IR_DMAC_DMAC1I,IR_DMAC_DMAC2I,IR_DMAC_DMAC3I,IR_DMAC_DMAC74I,
IR_OST_OSTDI,
IR_EXDMAC_EXDMAC0I,IR_EXDMAC_EXDMAC1I,
IR_PERIB_INTB128,IR_PERIB_INTB129,IR_PERIB_INTB130,IR_PERIB_INTB131,IR_PERIB_INTB132,
IR_PERIB_INTB133,IR_PERIB_INTB134,IR_PERIB_INTB135,IR_PERIB_INTB136,IR_PERIB_INTB137,
IR_PERIB_INTB138,IR_PERIB_INTB139,IR_PERIB_INTB140,IR_PERIB_INTB141,IR_PERIB_INTB142,
IR_PERIB_INTB143,IR_PERIB_INTB144,IR_PERIB_INTB145,IR_PERIB_INTB146,IR_PERIB_INTB147,
IR_PERIB_INTB148,IR_PERIB_INTB149,IR_PERIB_INTB150,IR_PERIB_INTB151,IR_PERIB_INTB152,
IR_PERIB_INTB153,IR_PERIB_INTB154,IR_PERIB_INTB155,IR_PERIB_INTB156,IR_PERIB_INTB157,
IR_PERIB_INTB158,IR_PERIB_INTB159,IR_PERIB_INTB160,IR_PERIB_INTB161,IR_PERIB_INTB162,
IR_PERIB_INTB163,IR_PERIB_INTB164,IR_PERIB_INTB165,IR_PERIB_INTB166,IR_PERIB_INTB167,
IR_PERIB_INTB168,IR_PERIB_INTB169,IR_PERIB_INTB170,IR_PERIB_INTB171,IR_PERIB_INTB172,
IR_PERIB_INTB173,IR_PERIB_INTB174,IR_PERIB_INTB175,IR_PERIB_INTB176,IR_PERIB_INTB177,
IR_PERIB_INTB178,IR_PERIB_INTB179,IR_PERIB_INTB180,IR_PERIB_INTB181,IR_PERIB_INTB182,
IR_PERIB_INTB183,IR_PERIB_INTB184,IR_PERIB_INTB185,IR_PERIB_INTB186,IR_PERIB_INTB187,
IR_PERIB_INTB188,IR_PERIB_INTB189,IR_PERIB_INTB190,IR_PERIB_INTB191,IR_PERIB_INTB192,
IR_PERIB_INTB193,IR_PERIB_INTB194,IR_PERIB_INTB195,IR_PERIB_INTB196,IR_PERIB_INTB197,
IR_PERIB_INTB198,IR_PERIB_INTB199,IR_PERIB_INTB200,IR_PERIB_INTB201,IR_PERIB_INTB202,
IR_PERIB_INTB203,IR_PERIB_INTB204,IR_PERIB_INTB205,IR_PERIB_INTB206,IR_PERIB_INTB207,
IR_PERIA_INTA208,IR_PERIA_INTA209,IR_PERIA_INTA210,IR_PERIA_INTA211,IR_PERIA_INTA212,
IR_PERIA_INTA213,IR_PERIA_INTA214,IR_PERIA_INTA215,IR_PERIA_INTA216,IR_PERIA_INTA217,
IR_PERIA_INTA218,IR_PERIA_INTA219,IR_PERIA_INTA220,IR_PERIA_INTA221,IR_PERIA_INTA222,
IR_PERIA_INTA223,IR_PERIA_INTA224,IR_PERIA_INTA225,IR_PERIA_INTA226,IR_PERIA_INTA227,
IR_PERIA_INTA228,IR_PERIA_INTA229,IR_PERIA_INTA230,IR_PERIA_INTA231,IR_PERIA_INTA232,
IR_PERIA_INTA233,IR_PERIA_INTA234,IR_PERIA_INTA235,IR_PERIA_INTA236,IR_PERIA_INTA237,
IR_PERIA_INTA238,IR_PERIA_INTA239,IR_PERIA_INTA240,IR_PERIA_INTA241,IR_PERIA_INTA242,
IR_PERIA_INTA243,IR_PERIA_INTA244,IR_PERIA_INTA245,IR_PERIA_INTA246,IR_PERIA_INTA247,
IR_PERIA_INTA248,IR_PERIA_INTA249,IR_PERIA_INTA250,IR_PERIA_INTA251,IR_PERIA_INTA252,
IR_PERIA_INTA253,IR_PERIA_INTA254,IR_PERIA_INTA255
} enum_ir_t;

typedef enum enum_dtce {
DTCE_ICU_SWINT2=26,DTCE_ICU_SWINT,
DTCE_CMT0_CMI0,
DTCE_CMT1_CMI1,
DTCE_CMTW0_CMWI0,
DTCE_CMTW1_CMWI1,
DTCE_USB0_D0FIFO0=34,DTCE_USB0_D1FIFO0,
DTCE_RSPI0_SPRI0=38,DTCE_RSPI0_SPTI0,
DTCE_RSPI1_SPRI1,DTCE_RSPI1_SPTI1,
DTCE_QSPI_SPRI,DTCE_QSPI_SPTI,
DTCE_SDHI_SBFAI,
DTCE_MMCIF_MBFAI,
DTCE_SSIE0_SSITXI0,DTCE_SSIE0_SSIRXI0,
DTCE_SSIE1_SSIRTI1,
DTCE_RIIC1_RXI1=50,DTCE_RIIC1_TXI1,
DTCE_RIIC0_RXI0,DTCE_RIIC0_TXI0,
DTCE_RIIC2_RXI2,DTCE_RIIC2_TXI2,
DTCE_SCI0_RXI0=58,DTCE_SCI0_TXI0,
DTCE_SCI1_RXI1,DTCE_SCI1_TXI1,
DTCE_SCI2_RXI2,DTCE_SCI2_TXI2,
DTCE_ICU_IRQ0,DTCE_ICU_IRQ1,DTCE_ICU_IRQ2,DTCE_ICU_IRQ3,DTCE_ICU_IRQ4,DTCE_ICU_IRQ5,DTCE_ICU_IRQ6,DTCE_ICU_IRQ7,
DTCE_ICU_IRQ8,DTCE_ICU_IRQ9,DTCE_ICU_IRQ10,DTCE_ICU_IRQ11,DTCE_ICU_IRQ12,DTCE_ICU_IRQ13,DTCE_ICU_IRQ14,DTCE_ICU_IRQ15,
DTCE_SCI3_RXI3,DTCE_SCI3_TXI3,
DTCE_SCI4_RXI4,DTCE_SCI4_TXI4,
DTCE_SCI5_RXI5,DTCE_SCI5_TXI5,
DTCE_SCI6_RXI6,DTCE_SCI6_TXI6,
DTCE_PDC_PCDFI=97,
DTCE_SCI7_RXI7,DTCE_SCI7_TXI7,
DTCE_SCI8_RXI8,DTCE_SCI8_TXI8,
DTCE_SCI9_RXI9,DTCE_SCI9_TXI9,
DTCE_SCI10_RXI10,DTCE_SCI10_TXI10,
DTCE_RSPI2_SPRI2=108,DTCE_RSPI2_SPTI2,
DTCE_SCI11_RXI11=114,DTCE_SCI11_TXI11,
DTCE_SCI12_RXI12,DTCE_SCI12_TXI12,
DTCE_DMAC_DMAC0I=120,DTCE_DMAC_DMAC1I,DTCE_DMAC_DMAC2I,DTCE_DMAC_DMAC3I,
DTCE_EXDMAC_EXDMAC0I=126,DTCE_EXDMAC_EXDMAC1I,
DTCE_PERIB_INTB128,DTCE_PERIB_INTB129,DTCE_PERIB_INTB130,DTCE_PERIB_INTB131,DTCE_PERIB_INTB132,
DTCE_PERIB_INTB133,DTCE_PERIB_INTB134,DTCE_PERIB_INTB135,DTCE_PERIB_INTB136,DTCE_PERIB_INTB137,
DTCE_PERIB_INTB138,DTCE_PERIB_INTB139,DTCE_PERIB_INTB140,DTCE_PERIB_INTB141,DTCE_PERIB_INTB142,
DTCE_PERIB_INTB143,DTCE_PERIB_INTB144,DTCE_PERIB_INTB145,DTCE_PERIB_INTB146,DTCE_PERIB_INTB147,
DTCE_PERIB_INTB148,DTCE_PERIB_INTB149,DTCE_PERIB_INTB150,DTCE_PERIB_INTB151,DTCE_PERIB_INTB152,
DTCE_PERIB_INTB153,DTCE_PERIB_INTB154,DTCE_PERIB_INTB155,DTCE_PERIB_INTB156,DTCE_PERIB_INTB157,
DTCE_PERIB_INTB158,DTCE_PERIB_INTB159,DTCE_PERIB_INTB160,DTCE_PERIB_INTB161,DTCE_PERIB_INTB162,
DTCE_PERIB_INTB163,DTCE_PERIB_INTB164,DTCE_PERIB_INTB165,DTCE_PERIB_INTB166,DTCE_PERIB_INTB167,
DTCE_PERIB_INTB168,DTCE_PERIB_INTB169,DTCE_PERIB_INTB170,DTCE_PERIB_INTB171,DTCE_PERIB_INTB172,
DTCE_PERIB_INTB173,DTCE_PERIB_INTB174,DTCE_PERIB_INTB175,DTCE_PERIB_INTB176,DTCE_PERIB_INTB177,
DTCE_PERIB_INTB178,DTCE_PERIB_INTB179,DTCE_PERIB_INTB180,DTCE_PERIB_INTB181,DTCE_PERIB_INTB182,
DTCE_PERIB_INTB183,DTCE_PERIB_INTB184,DTCE_PERIB_INTB185,DTCE_PERIB_INTB186,DTCE_PERIB_INTB187,
DTCE_PERIB_INTB188,DTCE_PERIB_INTB189,DTCE_PERIB_INTB190,DTCE_PERIB_INTB191,DTCE_PERIB_INTB192,
DTCE_PERIB_INTB193,DTCE_PERIB_INTB194,DTCE_PERIB_INTB195,DTCE_PERIB_INTB196,DTCE_PERIB_INTB197,
DTCE_PERIB_INTB198,DTCE_PERIB_INTB199,DTCE_PERIB_INTB200,DTCE_PERIB_INTB201,DTCE_PERIB_INTB202,
DTCE_PERIB_INTB203,DTCE_PERIB_INTB204,DTCE_PERIB_INTB205,DTCE_PERIB_INTB206,DTCE_PERIB_INTB207,
DTCE_PERIA_INTA208,DTCE_PERIA_INTA209,DTCE_PERIA_INTA210,DTCE_PERIA_INTA211,DTCE_PERIA_INTA212,
DTCE_PERIA_INTA213,DTCE_PERIA_INTA214,DTCE_PERIA_INTA215,DTCE_PERIA_INTA216,DTCE_PERIA_INTA217,
DTCE_PERIA_INTA218,DTCE_PERIA_INTA219,DTCE_PERIA_INTA220,DTCE_PERIA_INTA221,DTCE_PERIA_INTA222,
DTCE_PERIA_INTA223,DTCE_PERIA_INTA224,DTCE_PERIA_INTA225,DTCE_PERIA_INTA226,DTCE_PERIA_INTA227,
DTCE_PERIA_INTA228,DTCE_PERIA_INTA229,DTCE_PERIA_INTA230,DTCE_PERIA_INTA231,DTCE_PERIA_INTA232,
DTCE_PERIA_INTA233,DTCE_PERIA_INTA234,DTCE_PERIA_INTA235,DTCE_PERIA_INTA236,DTCE_PERIA_INTA237,
DTCE_PERIA_INTA238,DTCE_PERIA_INTA239,DTCE_PERIA_INTA240,DTCE_PERIA_INTA241,DTCE_PERIA_INTA242,
DTCE_PERIA_INTA243,DTCE_PERIA_INTA244,DTCE_PERIA_INTA245,DTCE_PERIA_INTA246,DTCE_PERIA_INTA247,
DTCE_PERIA_INTA248,DTCE_PERIA_INTA249,DTCE_PERIA_INTA250,DTCE_PERIA_INTA251,DTCE_PERIA_INTA252,
DTCE_PERIA_INTA253,DTCE_PERIA_INTA254,DTCE_PERIA_INTA255
} enum_dtce_t;

typedef enum enum_ier {
IER_BSC_BUSERR=0x02,
IER_ICU_GROUPIE0=0x02,
IER_RAM_RAMERR=0x02,
IER_FCU_FIFERR=0x02,IER_FCU_FRDYI=0x02,
IER_ICU_SWINT2=0x03,IER_ICU_SWINT=0x03,
IER_CMT0_CMI0=0x03,
IER_CMT1_CMI1=0x03,
IER_CMTW0_CMWI0=0x03,
IER_CMTW1_CMWI1=0x03,
IER_USB0_D0FIFO0=0x04,IER_USB0_D1FIFO0=0x04,
IER_RSPI0_SPRI0=0x04,IER_RSPI0_SPTI0=0x04,
IER_RSPI1_SPRI1=0x05,IER_RSPI1_SPTI1=0x05,
IER_QSPI_SPRI=0x05,IER_QSPI_SPTI=0x05,
IER_SDHI_SBFAI=0x05,
IER_MMCIF_MBFAI=0x05,
IER_SSIE0_SSITXI0=0x05,IER_SSIE0_SSIRXI0=0x05,
IER_SSIE1_SSIRTI1=0x06,
IER_RIIC1_RXI1=0x06,IER_RIIC1_TXI1=0x06,
IER_RIIC0_RXI0=0x06,IER_RIIC0_TXI0=0x06,
IER_RIIC2_RXI2=0x06,IER_RIIC2_TXI2=0x06,
IER_SCI0_RXI0=0x07,IER_SCI0_TXI0=0x07,
IER_SCI1_RXI1=0x07,IER_SCI1_TXI1=0x07,
IER_SCI2_RXI2=0x07,IER_SCI2_TXI2=0x07,
IER_ICU_IRQ0=0x08,IER_ICU_IRQ1=0x08,IER_ICU_IRQ2=0x08,IER_ICU_IRQ3=0x08,IER_ICU_IRQ4=0x08,IER_ICU_IRQ5=0x08,IER_ICU_IRQ6=0x08,IER_ICU_IRQ7=0x08,
IER_ICU_IRQ8=0x09,IER_ICU_IRQ9=0x09,IER_ICU_IRQ10=0x09,IER_ICU_IRQ11=0x09,IER_ICU_IRQ12=0x09,IER_ICU_IRQ13=0x09,IER_ICU_IRQ14=0x09,IER_ICU_IRQ15=0x09,
IER_SCI3_RXI3=0x0A,IER_SCI3_TXI3=0x0A,
IER_SCI4_RXI4=0x0A,IER_SCI4_TXI4=0x0A,
IER_SCI5_RXI5=0x0A,IER_SCI5_TXI5=0x0A,
IER_SCI6_RXI6=0x0A,IER_SCI6_TXI6=0x0A,
IER_LVD1_LVD1=0x0B,
IER_LVD2_LVD2=0x0B,
IER_USB0_USBR0=0x0B,
IER_RTC_ALM=0x0B,IER_RTC_PRD=0x0B,
IER_IWDT_IWUNI=0x0B,
IER_WDT_WUNI=0x0C,
IER_PDC_PCDFI=0x0C,
IER_SCI7_RXI7=0x0C,IER_SCI7_TXI7=0x0C,
IER_SCI8_RXI8=0x0C,IER_SCI8_TXI8=0x0C,
IER_SCI9_RXI9=0x0C,IER_SCI9_TXI9=0x0C,
IER_SCI10_RXI10=0x0D,IER_SCI10_TXI10=0x0D,
IER_ICU_GROUPBE0=0x0D,IER_ICU_GROUPBL2=0x0D,
IER_RSPI2_SPRI2=0x0D,IER_RSPI2_SPTI2=0x0D,
IER_ICU_GROUPBL0=0x0D,IER_ICU_GROUPBL1=0x0D,IER_ICU_GROUPAL0=0x0E,IER_ICU_GROUPAL1=0x0E,
IER_SCI11_RXI11=0x0E,IER_SCI11_TXI11=0x0E,
IER_SCI12_RXI12=0x0E,IER_SCI12_TXI12=0x0E,
IER_DMAC_DMAC0I=0x0F,IER_DMAC_DMAC1I=0x0F,IER_DMAC_DMAC2I=0x0F,IER_DMAC_DMAC3I=0x0F,IER_DMAC_DMAC74I=0x0F,
IER_OST_OSTDI=0x0F,
IER_EXDMAC_EXDMAC0I=0x0F,IER_EXDMAC_EXDMAC1I=0x0F,
IER_PERIB_INTB128=0x10,IER_PERIB_INTB129=0x10,IER_PERIB_INTB130=0x10,IER_PERIB_INTB131=0x10,IER_PERIB_INTB132=0x10,
IER_PERIB_INTB133=0x10,IER_PERIB_INTB134=0x10,IER_PERIB_INTB135=0x10,IER_PERIB_INTB136=0x11,IER_PERIB_INTB137=0x11,
IER_PERIB_INTB138=0x11,IER_PERIB_INTB139=0x11,IER_PERIB_INTB140=0x11,IER_PERIB_INTB141=0x11,IER_PERIB_INTB142=0x11,
IER_PERIB_INTB143=0x11,IER_PERIB_INTB144=0x12,IER_PERIB_INTB145=0x12,IER_PERIB_INTB146=0x12,IER_PERIB_INTB147=0x12,
IER_PERIB_INTB148=0x12,IER_PERIB_INTB149=0x12,IER_PERIB_INTB150=0x12,IER_PERIB_INTB151=0x12,IER_PERIB_INTB152=0x13,
IER_PERIB_INTB153=0x13,IER_PERIB_INTB154=0x13,IER_PERIB_INTB155=0x13,IER_PERIB_INTB156=0x13,IER_PERIB_INTB157=0x13,
IER_PERIB_INTB158=0x13,IER_PERIB_INTB159=0x13,IER_PERIB_INTB160=0x14,IER_PERIB_INTB161=0x14,IER_PERIB_INTB162=0x14,
IER_PERIB_INTB163=0x14,IER_PERIB_INTB164=0x14,IER_PERIB_INTB165=0x14,IER_PERIB_INTB166=0x14,IER_PERIB_INTB167=0x14,
IER_PERIB_INTB168=0x15,IER_PERIB_INTB169=0x15,IER_PERIB_INTB170=0x15,IER_PERIB_INTB171=0x15,IER_PERIB_INTB172=0x15,
IER_PERIB_INTB173=0x15,IER_PERIB_INTB174=0x15,IER_PERIB_INTB175=0x15,IER_PERIB_INTB176=0x16,IER_PERIB_INTB177=0x16,
IER_PERIB_INTB178=0x16,IER_PERIB_INTB179=0x16,IER_PERIB_INTB180=0x16,IER_PERIB_INTB181=0x16,IER_PERIB_INTB182=0x16,
IER_PERIB_INTB183=0x16,IER_PERIB_INTB184=0x17,IER_PERIB_INTB185=0x17,IER_PERIB_INTB186=0x17,IER_PERIB_INTB187=0x17,
IER_PERIB_INTB188=0x17,IER_PERIB_INTB189=0x17,IER_PERIB_INTB190=0x17,IER_PERIB_INTB191=0x17,IER_PERIB_INTB192=0x18,
IER_PERIB_INTB193=0x18,IER_PERIB_INTB194=0x18,IER_PERIB_INTB195=0x18,IER_PERIB_INTB196=0x18,IER_PERIB_INTB197=0x18,
IER_PERIB_INTB198=0x18,IER_PERIB_INTB199=0x18,IER_PERIB_INTB200=0x19,IER_PERIB_INTB201=0x19,IER_PERIB_INTB202=0x19,
IER_PERIB_INTB203=0x19,IER_PERIB_INTB204=0x19,IER_PERIB_INTB205=0x19,IER_PERIB_INTB206=0x19,IER_PERIB_INTB207=0x19,
IER_PERIA_INTA208=0x1A,IER_PERIA_INTA209=0x1A,IER_PERIA_INTA210=0x1A,IER_PERIA_INTA211=0x1A,IER_PERIA_INTA212=0x1A,
IER_PERIA_INTA213=0x1A,IER_PERIA_INTA214=0x1A,IER_PERIA_INTA215=0x1A,IER_PERIA_INTA216=0x1B,IER_PERIA_INTA217=0x1B,
IER_PERIA_INTA218=0x1B,IER_PERIA_INTA219=0x1B,IER_PERIA_INTA220=0x1B,IER_PERIA_INTA221=0x1B,IER_PERIA_INTA222=0x1B,
IER_PERIA_INTA223=0x1B,IER_PERIA_INTA224=0x1C,IER_PERIA_INTA225=0x1C,IER_PERIA_INTA226=0x1C,IER_PERIA_INTA227=0x1C,
IER_PERIA_INTA228=0x1C,IER_PERIA_INTA229=0x1C,IER_PERIA_INTA230=0x1C,IER_PERIA_INTA231=0x1C,IER_PERIA_INTA232=0x1D,
IER_PERIA_INTA233=0x1D,IER_PERIA_INTA234=0x1D,IER_PERIA_INTA235=0x1D,IER_PERIA_INTA236=0x1D,IER_PERIA_INTA237=0x1D,
IER_PERIA_INTA238=0x1D,IER_PERIA_INTA239=0x1D,IER_PERIA_INTA240=0x1E,IER_PERIA_INTA241=0x1E,IER_PERIA_INTA242=0x1E,
IER_PERIA_INTA243=0x1E,IER_PERIA_INTA244=0x1E,IER_PERIA_INTA245=0x1E,IER_PERIA_INTA246=0x1E,IER_PERIA_INTA247=0x1E,
IER_PERIA_INTA248=0x1F,IER_PERIA_INTA249=0x1F,IER_PERIA_INTA250=0x1F,IER_PERIA_INTA251=0x1F,IER_PERIA_INTA252=0x1F,
IER_PERIA_INTA253=0x1F,IER_PERIA_INTA254=0x1F,IER_PERIA_INTA255=0x1F
} enum_ier_t;

typedef enum enum_ipr {
IPR_BSC_BUSERR=0,
IPR_ICU_GROUPIE0=0,
IPR_RAM_RAMERR=0,
IPR_FCU_FIFERR=1,IPR_FCU_FRDYI=2,
IPR_ICU_SWINT2=3,IPR_ICU_SWINT=3,
IPR_CMT0_CMI0=4,
IPR_CMT1_CMI1=5,
IPR_CMTW0_CMWI0=6,
IPR_CMTW1_CMWI1=7,
IPR_USB0_D0FIFO0=34,IPR_USB0_D1FIFO0=35,
IPR_RSPI0_SPRI0=38,IPR_RSPI0_SPTI0=39,
IPR_RSPI1_SPRI1=40,IPR_RSPI1_SPTI1=41,
IPR_QSPI_SPRI=42,IPR_QSPI_SPTI=43,
IPR_SDHI_SBFAI=44,
IPR_MMCIF_MBFAI=45,
IPR_SSIE0_SSITXI0=46,IPR_SSIE0_SSIRXI0=47,
IPR_SSIE1_SSIRTI1=48,
IPR_RIIC1_RXI1=50,IPR_RIIC1_TXI1=51,
IPR_RIIC0_RXI0=52,IPR_RIIC0_TXI0=53,
IPR_RIIC2_RXI2=54,IPR_RIIC2_TXI2=55,
IPR_SCI0_RXI0=58,IPR_SCI0_TXI0=59,
IPR_SCI1_RXI1=60,IPR_SCI1_TXI1=61,
IPR_SCI2_RXI2=62,IPR_SCI2_TXI2=63,
IPR_ICU_IRQ0=64,IPR_ICU_IRQ1=65,IPR_ICU_IRQ2=66,IPR_ICU_IRQ3=67,IPR_ICU_IRQ4=68,IPR_ICU_IRQ5=69,IPR_ICU_IRQ6=70,IPR_ICU_IRQ7=71,
IPR_ICU_IRQ8=72,IPR_ICU_IRQ9=73,IPR_ICU_IRQ10=74,IPR_ICU_IRQ11=75,IPR_ICU_IRQ12=76,IPR_ICU_IRQ13=77,IPR_ICU_IRQ14=78,IPR_ICU_IRQ15=79,
IPR_SCI3_RXI3=80,IPR_SCI3_TXI3=81,
IPR_SCI4_RXI4=82,IPR_SCI4_TXI4=83,
IPR_SCI5_RXI5=84,IPR_SCI5_TXI5=85,
IPR_SCI6_RXI6=86,IPR_SCI6_TXI6=87,
IPR_LVD1_LVD1=88,
IPR_LVD2_LVD2=89,
IPR_USB0_USBR0=90,
IPR_RTC_ALM=92,IPR_RTC_PRD=93,
IPR_IWDT_IWUNI=95,
IPR_WDT_WUNI=96,
IPR_PDC_PCDFI=97,
IPR_SCI7_RXI7=98,IPR_SCI7_TXI7=99,
IPR_SCI8_RXI8=100,IPR_SCI8_TXI8=101,
IPR_SCI9_RXI9=102,IPR_SCI9_TXI9=103,
IPR_SCI10_RXI10=104,IPR_SCI10_TXI10=105,
IPR_ICU_GROUPBE0=106,IPR_ICU_GROUPBL2=107,
IPR_RSPI2_SPRI2=108,IPR_RSPI2_SPTI2=109,
IPR_ICU_GROUPBL0=110,IPR_ICU_GROUPBL1=111,IPR_ICU_GROUPAL0=112,IPR_ICU_GROUPAL1=113,
IPR_SCI11_RXI11=114,IPR_SCI11_TXI11=115,
IPR_SCI12_RXI12=116,IPR_SCI12_TXI12=117,
IPR_DMAC_DMAC0I=120,IPR_DMAC_DMAC1I=121,IPR_DMAC_DMAC2I=122,IPR_DMAC_DMAC3I=123,IPR_DMAC_DMAC74I=124,
IPR_OST_OSTDI=125,
IPR_EXDMAC_EXDMAC0I=126,IPR_EXDMAC_EXDMAC1I=127,
IPR_PERIB_INTB128=128,IPR_PERIB_INTB129=129,IPR_PERIB_INTB130=130,IPR_PERIB_INTB131=131,IPR_PERIB_INTB132=132,
IPR_PERIB_INTB133=133,IPR_PERIB_INTB134=134,IPR_PERIB_INTB135=135,IPR_PERIB_INTB136=136,IPR_PERIB_INTB137=137,
IPR_PERIB_INTB138=138,IPR_PERIB_INTB139=139,IPR_PERIB_INTB140=140,IPR_PERIB_INTB141=141,IPR_PERIB_INTB142=142,
IPR_PERIB_INTB143=143,IPR_PERIB_INTB144=144,IPR_PERIB_INTB145=145,IPR_PERIB_INTB146=146,IPR_PERIB_INTB147=147,
IPR_PERIB_INTB148=148,IPR_PERIB_INTB149=149,IPR_PERIB_INTB150=150,IPR_PERIB_INTB151=151,IPR_PERIB_INTB152=152,
IPR_PERIB_INTB153=153,IPR_PERIB_INTB154=154,IPR_PERIB_INTB155=155,IPR_PERIB_INTB156=156,IPR_PERIB_INTB157=157,
IPR_PERIB_INTB158=158,IPR_PERIB_INTB159=159,IPR_PERIB_INTB160=160,IPR_PERIB_INTB161=161,IPR_PERIB_INTB162=162,
IPR_PERIB_INTB163=163,IPR_PERIB_INTB164=164,IPR_PERIB_INTB165=165,IPR_PERIB_INTB166=166,IPR_PERIB_INTB167=167,
IPR_PERIB_INTB168=168,IPR_PERIB_INTB169=169,IPR_PERIB_INTB170=170,IPR_PERIB_INTB171=171,IPR_PERIB_INTB172=172,
IPR_PERIB_INTB173=173,IPR_PERIB_INTB174=174,IPR_PERIB_INTB175=175,IPR_PERIB_INTB176=176,IPR_PERIB_INTB177=177,
IPR_PERIB_INTB178=178,IPR_PERIB_INTB179=179,IPR_PERIB_INTB180=180,IPR_PERIB_INTB181=181,IPR_PERIB_INTB182=182,
IPR_PERIB_INTB183=183,IPR_PERIB_INTB184=184,IPR_PERIB_INTB185=185,IPR_PERIB_INTB186=186,IPR_PERIB_INTB187=187,
IPR_PERIB_INTB188=188,IPR_PERIB_INTB189=189,IPR_PERIB_INTB190=190,IPR_PERIB_INTB191=191,IPR_PERIB_INTB192=192,
IPR_PERIB_INTB193=193,IPR_PERIB_INTB194=194,IPR_PERIB_INTB195=195,IPR_PERIB_INTB196=196,IPR_PERIB_INTB197=197,
IPR_PERIB_INTB198=198,IPR_PERIB_INTB199=199,IPR_PERIB_INTB200=200,IPR_PERIB_INTB201=201,IPR_PERIB_INTB202=202,
IPR_PERIB_INTB203=203,IPR_PERIB_INTB204=204,IPR_PERIB_INTB205=205,IPR_PERIB_INTB206=206,IPR_PERIB_INTB207=207,
IPR_PERIA_INTA208=208,IPR_PERIA_INTA209=209,IPR_PERIA_INTA210=210,IPR_PERIA_INTA211=211,IPR_PERIA_INTA212=212,
IPR_PERIA_INTA213=213,IPR_PERIA_INTA214=214,IPR_PERIA_INTA215=215,IPR_PERIA_INTA216=216,IPR_PERIA_INTA217=217,
IPR_PERIA_INTA218=218,IPR_PERIA_INTA219=219,IPR_PERIA_INTA220=220,IPR_PERIA_INTA221=221,IPR_PERIA_INTA222=222,
IPR_PERIA_INTA223=223,IPR_PERIA_INTA224=224,IPR_PERIA_INTA225=225,IPR_PERIA_INTA226=226,IPR_PERIA_INTA227=227,
IPR_PERIA_INTA228=228,IPR_PERIA_INTA229=229,IPR_PERIA_INTA230=230,IPR_PERIA_INTA231=231,IPR_PERIA_INTA232=232,
IPR_PERIA_INTA233=233,IPR_PERIA_INTA234=234,IPR_PERIA_INTA235=235,IPR_PERIA_INTA236=236,IPR_PERIA_INTA237=237,
IPR_PERIA_INTA238=238,IPR_PERIA_INTA239=239,IPR_PERIA_INTA240=240,IPR_PERIA_INTA241=241,IPR_PERIA_INTA242=242,
IPR_PERIA_INTA243=243,IPR_PERIA_INTA244=244,IPR_PERIA_INTA245=245,IPR_PERIA_INTA246=246,IPR_PERIA_INTA247=247,
IPR_PERIA_INTA248=248,IPR_PERIA_INTA249=249,IPR_PERIA_INTA250=250,IPR_PERIA_INTA251=251,IPR_PERIA_INTA252=252,
IPR_PERIA_INTA253=253,IPR_PERIA_INTA254=254,IPR_PERIA_INTA255=255,
IPR_ICU_SWI=3,
IPR_CMT0_=4,
IPR_CMT1_=5,
IPR_CMTW0_=6,
IPR_CMTW1_=7,
IPR_SDHI_=44,
IPR_MMCIF_=45,
IPR_SSIE1_=48,
IPR_LVD1_=88,
IPR_LVD2_=89,
IPR_IWDT_=95,
IPR_WDT_=96,
IPR_PDC_=97,
IPR_OST_=125
} enum_ipr_t;


#pragma pack(4)


typedef struct st_bsc {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char STSCLR : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char STSCLR : 1;
#endif
	} BIT;
	} BERCLR;
	char           wk0[3];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IGAEN : 1;
			unsigned char TOEN : 1;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char TOEN : 1;
			unsigned char IGAEN : 1;
#endif
	} BIT;
	} BEREN;
	char           wk1[3];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IA : 1;
			unsigned char TO : 1;
			unsigned char  : 2;
			unsigned char MST : 3;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char MST : 3;
			unsigned char  : 2;
			unsigned char TO : 1;
			unsigned char IA : 1;
#endif
	} BIT;
	} BERSR1;
	char           wk2[1];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 3;
			unsigned short ADDR : 13;
#else
			unsigned short ADDR : 13;
			unsigned short  : 3;
#endif
	} BIT;
	} BERSR2;
	char           wk3[4];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short BPRA : 2;
			unsigned short BPRO : 2;
			unsigned short BPIB : 2;
			unsigned short BPGB : 2;
			unsigned short BPHB : 2;
			unsigned short BPFB : 2;
			unsigned short BPEB : 2;
			unsigned short  : 2;
#else
			unsigned short  : 2;
			unsigned short BPEB : 2;
			unsigned short BPFB : 2;
			unsigned short BPHB : 2;
			unsigned short BPGB : 2;
			unsigned short BPIB : 2;
			unsigned short BPRO : 2;
			unsigned short BPRA : 2;
#endif
	} BIT;
	} BUSPRI;
	char           wk4[7408];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short WRMOD : 1;
			unsigned short  : 2;
			unsigned short EWENB : 1;
			unsigned short  : 4;
			unsigned short PRENB : 1;
			unsigned short PWENB : 1;
			unsigned short  : 5;
			unsigned short PRMOD : 1;
#else
			unsigned short PRMOD : 1;
			unsigned short  : 5;
			unsigned short PWENB : 1;
			unsigned short PRENB : 1;
			unsigned short  : 4;
			unsigned short EWENB : 1;
			unsigned short  : 2;
			unsigned short WRMOD : 1;
#endif
	} BIT;
	} CS0MOD;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CSPWWAIT : 3;
			unsigned long  : 5;
			unsigned long CSPRWAIT : 3;
			unsigned long  : 5;
			unsigned long CSWWAIT : 5;
			unsigned long  : 3;
			unsigned long CSRWAIT : 5;
			unsigned long  : 3;
#else
			unsigned long  : 3;
			unsigned long CSRWAIT : 5;
			unsigned long  : 3;
			unsigned long CSWWAIT : 5;
			unsigned long  : 5;
			unsigned long CSPRWAIT : 3;
			unsigned long  : 5;
			unsigned long CSPWWAIT : 3;
#endif
	} BIT;
	} CS0WCR1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CSROFF : 3;
			unsigned long  : 1;
			unsigned long CSWOFF : 3;
			unsigned long  : 1;
			unsigned long WDOFF : 3;
			unsigned long  : 1;
			unsigned long AWAIT : 2;
			unsigned long  : 2;
			unsigned long RDON : 3;
			unsigned long  : 1;
			unsigned long WRON : 3;
			unsigned long  : 1;
			unsigned long WDON : 3;
			unsigned long  : 1;
			unsigned long CSON : 3;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long CSON : 3;
			unsigned long  : 1;
			unsigned long WDON : 3;
			unsigned long  : 1;
			unsigned long WRON : 3;
			unsigned long  : 1;
			unsigned long RDON : 3;
			unsigned long  : 2;
			unsigned long AWAIT : 2;
			unsigned long  : 1;
			unsigned long WDOFF : 3;
			unsigned long  : 1;
			unsigned long CSWOFF : 3;
			unsigned long  : 1;
			unsigned long CSROFF : 3;
#endif
	} BIT;
	} CS0WCR2;
	char           wk5[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short WRMOD : 1;
			unsigned short  : 2;
			unsigned short EWENB : 1;
			unsigned short  : 4;
			unsigned short PRENB : 1;
			unsigned short PWENB : 1;
			unsigned short  : 5;
			unsigned short PRMOD : 1;
#else
			unsigned short PRMOD : 1;
			unsigned short  : 5;
			unsigned short PWENB : 1;
			unsigned short PRENB : 1;
			unsigned short  : 4;
			unsigned short EWENB : 1;
			unsigned short  : 2;
			unsigned short WRMOD : 1;
#endif
	} BIT;
	} CS1MOD;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CSPWWAIT : 3;
			unsigned long  : 5;
			unsigned long CSPRWAIT : 3;
			unsigned long  : 5;
			unsigned long CSWWAIT : 5;
			unsigned long  : 3;
			unsigned long CSRWAIT : 5;
			unsigned long  : 3;
#else
			unsigned long  : 3;
			unsigned long CSRWAIT : 5;
			unsigned long  : 3;
			unsigned long CSWWAIT : 5;
			unsigned long  : 5;
			unsigned long CSPRWAIT : 3;
			unsigned long  : 5;
			unsigned long CSPWWAIT : 3;
#endif
	} BIT;
	} CS1WCR1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CSROFF : 3;
			unsigned long  : 1;
			unsigned long CSWOFF : 3;
			unsigned long  : 1;
			unsigned long WDOFF : 3;
			unsigned long  : 1;
			unsigned long AWAIT : 2;
			unsigned long  : 2;
			unsigned long RDON : 3;
			unsigned long  : 1;
			unsigned long WRON : 3;
			unsigned long  : 1;
			unsigned long WDON : 3;
			unsigned long  : 1;
			unsigned long CSON : 3;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long CSON : 3;
			unsigned long  : 1;
			unsigned long WDON : 3;
			unsigned long  : 1;
			unsigned long WRON : 3;
			unsigned long  : 1;
			unsigned long RDON : 3;
			unsigned long  : 2;
			unsigned long AWAIT : 2;
			unsigned long  : 1;
			unsigned long WDOFF : 3;
			unsigned long  : 1;
			unsigned long CSWOFF : 3;
			unsigned long  : 1;
			unsigned long CSROFF : 3;
#endif
	} BIT;
	} CS1WCR2;
	char           wk6[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short WRMOD : 1;
			unsigned short  : 2;
			unsigned short EWENB : 1;
			unsigned short  : 4;
			unsigned short PRENB : 1;
			unsigned short PWENB : 1;
			unsigned short  : 5;
			unsigned short PRMOD : 1;
#else
			unsigned short PRMOD : 1;
			unsigned short  : 5;
			unsigned short PWENB : 1;
			unsigned short PRENB : 1;
			unsigned short  : 4;
			unsigned short EWENB : 1;
			unsigned short  : 2;
			unsigned short WRMOD : 1;
#endif
	} BIT;
	} CS2MOD;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CSPWWAIT : 3;
			unsigned long  : 5;
			unsigned long CSPRWAIT : 3;
			unsigned long  : 5;
			unsigned long CSWWAIT : 5;
			unsigned long  : 3;
			unsigned long CSRWAIT : 5;
			unsigned long  : 3;
#else
			unsigned long  : 3;
			unsigned long CSRWAIT : 5;
			unsigned long  : 3;
			unsigned long CSWWAIT : 5;
			unsigned long  : 5;
			unsigned long CSPRWAIT : 3;
			unsigned long  : 5;
			unsigned long CSPWWAIT : 3;
#endif
	} BIT;
	} CS2WCR1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CSROFF : 3;
			unsigned long  : 1;
			unsigned long CSWOFF : 3;
			unsigned long  : 1;
			unsigned long WDOFF : 3;
			unsigned long  : 1;
			unsigned long AWAIT : 2;
			unsigned long  : 2;
			unsigned long RDON : 3;
			unsigned long  : 1;
			unsigned long WRON : 3;
			unsigned long  : 1;
			unsigned long WDON : 3;
			unsigned long  : 1;
			unsigned long CSON : 3;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long CSON : 3;
			unsigned long  : 1;
			unsigned long WDON : 3;
			unsigned long  : 1;
			unsigned long WRON : 3;
			unsigned long  : 1;
			unsigned long RDON : 3;
			unsigned long  : 2;
			unsigned long AWAIT : 2;
			unsigned long  : 1;
			unsigned long WDOFF : 3;
			unsigned long  : 1;
			unsigned long CSWOFF : 3;
			unsigned long  : 1;
			unsigned long CSROFF : 3;
#endif
	} BIT;
	} CS2WCR2;
	char           wk7[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short WRMOD : 1;
			unsigned short  : 2;
			unsigned short EWENB : 1;
			unsigned short  : 4;
			unsigned short PRENB : 1;
			unsigned short PWENB : 1;
			unsigned short  : 5;
			unsigned short PRMOD : 1;
#else
			unsigned short PRMOD : 1;
			unsigned short  : 5;
			unsigned short PWENB : 1;
			unsigned short PRENB : 1;
			unsigned short  : 4;
			unsigned short EWENB : 1;
			unsigned short  : 2;
			unsigned short WRMOD : 1;
#endif
	} BIT;
	} CS3MOD;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CSPWWAIT : 3;
			unsigned long  : 5;
			unsigned long CSPRWAIT : 3;
			unsigned long  : 5;
			unsigned long CSWWAIT : 5;
			unsigned long  : 3;
			unsigned long CSRWAIT : 5;
			unsigned long  : 3;
#else
			unsigned long  : 3;
			unsigned long CSRWAIT : 5;
			unsigned long  : 3;
			unsigned long CSWWAIT : 5;
			unsigned long  : 5;
			unsigned long CSPRWAIT : 3;
			unsigned long  : 5;
			unsigned long CSPWWAIT : 3;
#endif
	} BIT;
	} CS3WCR1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CSROFF : 3;
			unsigned long  : 1;
			unsigned long CSWOFF : 3;
			unsigned long  : 1;
			unsigned long WDOFF : 3;
			unsigned long  : 1;
			unsigned long AWAIT : 2;
			unsigned long  : 2;
			unsigned long RDON : 3;
			unsigned long  : 1;
			unsigned long WRON : 3;
			unsigned long  : 1;
			unsigned long WDON : 3;
			unsigned long  : 1;
			unsigned long CSON : 3;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long CSON : 3;
			unsigned long  : 1;
			unsigned long WDON : 3;
			unsigned long  : 1;
			unsigned long WRON : 3;
			unsigned long  : 1;
			unsigned long RDON : 3;
			unsigned long  : 2;
			unsigned long AWAIT : 2;
			unsigned long  : 1;
			unsigned long WDOFF : 3;
			unsigned long  : 1;
			unsigned long CSWOFF : 3;
			unsigned long  : 1;
			unsigned long CSROFF : 3;
#endif
	} BIT;
	} CS3WCR2;
	char           wk8[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short WRMOD : 1;
			unsigned short  : 2;
			unsigned short EWENB : 1;
			unsigned short  : 4;
			unsigned short PRENB : 1;
			unsigned short PWENB : 1;
			unsigned short  : 5;
			unsigned short PRMOD : 1;
#else
			unsigned short PRMOD : 1;
			unsigned short  : 5;
			unsigned short PWENB : 1;
			unsigned short PRENB : 1;
			unsigned short  : 4;
			unsigned short EWENB : 1;
			unsigned short  : 2;
			unsigned short WRMOD : 1;
#endif
	} BIT;
	} CS4MOD;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CSPWWAIT : 3;
			unsigned long  : 5;
			unsigned long CSPRWAIT : 3;
			unsigned long  : 5;
			unsigned long CSWWAIT : 5;
			unsigned long  : 3;
			unsigned long CSRWAIT : 5;
			unsigned long  : 3;
#else
			unsigned long  : 3;
			unsigned long CSRWAIT : 5;
			unsigned long  : 3;
			unsigned long CSWWAIT : 5;
			unsigned long  : 5;
			unsigned long CSPRWAIT : 3;
			unsigned long  : 5;
			unsigned long CSPWWAIT : 3;
#endif
	} BIT;
	} CS4WCR1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CSROFF : 3;
			unsigned long  : 1;
			unsigned long CSWOFF : 3;
			unsigned long  : 1;
			unsigned long WDOFF : 3;
			unsigned long  : 1;
			unsigned long AWAIT : 2;
			unsigned long  : 2;
			unsigned long RDON : 3;
			unsigned long  : 1;
			unsigned long WRON : 3;
			unsigned long  : 1;
			unsigned long WDON : 3;
			unsigned long  : 1;
			unsigned long CSON : 3;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long CSON : 3;
			unsigned long  : 1;
			unsigned long WDON : 3;
			unsigned long  : 1;
			unsigned long WRON : 3;
			unsigned long  : 1;
			unsigned long RDON : 3;
			unsigned long  : 2;
			unsigned long AWAIT : 2;
			unsigned long  : 1;
			unsigned long WDOFF : 3;
			unsigned long  : 1;
			unsigned long CSWOFF : 3;
			unsigned long  : 1;
			unsigned long CSROFF : 3;
#endif
	} BIT;
	} CS4WCR2;
	char           wk9[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short WRMOD : 1;
			unsigned short  : 2;
			unsigned short EWENB : 1;
			unsigned short  : 4;
			unsigned short PRENB : 1;
			unsigned short PWENB : 1;
			unsigned short  : 5;
			unsigned short PRMOD : 1;
#else
			unsigned short PRMOD : 1;
			unsigned short  : 5;
			unsigned short PWENB : 1;
			unsigned short PRENB : 1;
			unsigned short  : 4;
			unsigned short EWENB : 1;
			unsigned short  : 2;
			unsigned short WRMOD : 1;
#endif
	} BIT;
	} CS5MOD;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CSPWWAIT : 3;
			unsigned long  : 5;
			unsigned long CSPRWAIT : 3;
			unsigned long  : 5;
			unsigned long CSWWAIT : 5;
			unsigned long  : 3;
			unsigned long CSRWAIT : 5;
			unsigned long  : 3;
#else
			unsigned long  : 3;
			unsigned long CSRWAIT : 5;
			unsigned long  : 3;
			unsigned long CSWWAIT : 5;
			unsigned long  : 5;
			unsigned long CSPRWAIT : 3;
			unsigned long  : 5;
			unsigned long CSPWWAIT : 3;
#endif
	} BIT;
	} CS5WCR1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CSROFF : 3;
			unsigned long  : 1;
			unsigned long CSWOFF : 3;
			unsigned long  : 1;
			unsigned long WDOFF : 3;
			unsigned long  : 1;
			unsigned long AWAIT : 2;
			unsigned long  : 2;
			unsigned long RDON : 3;
			unsigned long  : 1;
			unsigned long WRON : 3;
			unsigned long  : 1;
			unsigned long WDON : 3;
			unsigned long  : 1;
			unsigned long CSON : 3;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long CSON : 3;
			unsigned long  : 1;
			unsigned long WDON : 3;
			unsigned long  : 1;
			unsigned long WRON : 3;
			unsigned long  : 1;
			unsigned long RDON : 3;
			unsigned long  : 2;
			unsigned long AWAIT : 2;
			unsigned long  : 1;
			unsigned long WDOFF : 3;
			unsigned long  : 1;
			unsigned long CSWOFF : 3;
			unsigned long  : 1;
			unsigned long CSROFF : 3;
#endif
	} BIT;
	} CS5WCR2;
	char           wk10[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short WRMOD : 1;
			unsigned short  : 2;
			unsigned short EWENB : 1;
			unsigned short  : 4;
			unsigned short PRENB : 1;
			unsigned short PWENB : 1;
			unsigned short  : 5;
			unsigned short PRMOD : 1;
#else
			unsigned short PRMOD : 1;
			unsigned short  : 5;
			unsigned short PWENB : 1;
			unsigned short PRENB : 1;
			unsigned short  : 4;
			unsigned short EWENB : 1;
			unsigned short  : 2;
			unsigned short WRMOD : 1;
#endif
	} BIT;
	} CS6MOD;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CSPWWAIT : 3;
			unsigned long  : 5;
			unsigned long CSPRWAIT : 3;
			unsigned long  : 5;
			unsigned long CSWWAIT : 5;
			unsigned long  : 3;
			unsigned long CSRWAIT : 5;
			unsigned long  : 3;
#else
			unsigned long  : 3;
			unsigned long CSRWAIT : 5;
			unsigned long  : 3;
			unsigned long CSWWAIT : 5;
			unsigned long  : 5;
			unsigned long CSPRWAIT : 3;
			unsigned long  : 5;
			unsigned long CSPWWAIT : 3;
#endif
	} BIT;
	} CS6WCR1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CSROFF : 3;
			unsigned long  : 1;
			unsigned long CSWOFF : 3;
			unsigned long  : 1;
			unsigned long WDOFF : 3;
			unsigned long  : 1;
			unsigned long AWAIT : 2;
			unsigned long  : 2;
			unsigned long RDON : 3;
			unsigned long  : 1;
			unsigned long WRON : 3;
			unsigned long  : 1;
			unsigned long WDON : 3;
			unsigned long  : 1;
			unsigned long CSON : 3;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long CSON : 3;
			unsigned long  : 1;
			unsigned long WDON : 3;
			unsigned long  : 1;
			unsigned long WRON : 3;
			unsigned long  : 1;
			unsigned long RDON : 3;
			unsigned long  : 2;
			unsigned long AWAIT : 2;
			unsigned long  : 1;
			unsigned long WDOFF : 3;
			unsigned long  : 1;
			unsigned long CSWOFF : 3;
			unsigned long  : 1;
			unsigned long CSROFF : 3;
#endif
	} BIT;
	} CS6WCR2;
	char           wk11[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short WRMOD : 1;
			unsigned short  : 2;
			unsigned short EWENB : 1;
			unsigned short  : 4;
			unsigned short PRENB : 1;
			unsigned short PWENB : 1;
			unsigned short  : 5;
			unsigned short PRMOD : 1;
#else
			unsigned short PRMOD : 1;
			unsigned short  : 5;
			unsigned short PWENB : 1;
			unsigned short PRENB : 1;
			unsigned short  : 4;
			unsigned short EWENB : 1;
			unsigned short  : 2;
			unsigned short WRMOD : 1;
#endif
	} BIT;
	} CS7MOD;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CSPWWAIT : 3;
			unsigned long  : 5;
			unsigned long CSPRWAIT : 3;
			unsigned long  : 5;
			unsigned long CSWWAIT : 5;
			unsigned long  : 3;
			unsigned long CSRWAIT : 5;
			unsigned long  : 3;
#else
			unsigned long  : 3;
			unsigned long CSRWAIT : 5;
			unsigned long  : 3;
			unsigned long CSWWAIT : 5;
			unsigned long  : 5;
			unsigned long CSPRWAIT : 3;
			unsigned long  : 5;
			unsigned long CSPWWAIT : 3;
#endif
	} BIT;
	} CS7WCR1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CSROFF : 3;
			unsigned long  : 1;
			unsigned long CSWOFF : 3;
			unsigned long  : 1;
			unsigned long WDOFF : 3;
			unsigned long  : 1;
			unsigned long AWAIT : 2;
			unsigned long  : 2;
			unsigned long RDON : 3;
			unsigned long  : 1;
			unsigned long WRON : 3;
			unsigned long  : 1;
			unsigned long WDON : 3;
			unsigned long  : 1;
			unsigned long CSON : 3;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long CSON : 3;
			unsigned long  : 1;
			unsigned long WDON : 3;
			unsigned long  : 1;
			unsigned long WRON : 3;
			unsigned long  : 1;
			unsigned long RDON : 3;
			unsigned long  : 2;
			unsigned long AWAIT : 2;
			unsigned long  : 1;
			unsigned long WDOFF : 3;
			unsigned long  : 1;
			unsigned long CSWOFF : 3;
			unsigned long  : 1;
			unsigned long CSROFF : 3;
#endif
	} BIT;
	} CS7WCR2;
	char           wk12[1926];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short EXENB : 1;
			unsigned short  : 3;
			unsigned short BSIZE : 2;
			unsigned short  : 2;
			unsigned short EMODE : 1;
			unsigned short  : 3;
			unsigned short MPXEN : 1;
			unsigned short  : 3;
#else
			unsigned short  : 3;
			unsigned short MPXEN : 1;
			unsigned short  : 3;
			unsigned short EMODE : 1;
			unsigned short  : 2;
			unsigned short BSIZE : 2;
			unsigned short  : 3;
			unsigned short EXENB : 1;
#endif
	} BIT;
	} CS0CR;
	char           wk13[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short RRCV : 4;
			unsigned short  : 4;
			unsigned short WRCV : 4;
			unsigned short  : 4;
#else
			unsigned short  : 4;
			unsigned short WRCV : 4;
			unsigned short  : 4;
			unsigned short RRCV : 4;
#endif
	} BIT;
	} CS0REC;
	char           wk14[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short EXENB : 1;
			unsigned short  : 3;
			unsigned short BSIZE : 2;
			unsigned short  : 2;
			unsigned short EMODE : 1;
			unsigned short  : 3;
			unsigned short MPXEN : 1;
			unsigned short  : 3;
#else
			unsigned short  : 3;
			unsigned short MPXEN : 1;
			unsigned short  : 3;
			unsigned short EMODE : 1;
			unsigned short  : 2;
			unsigned short BSIZE : 2;
			unsigned short  : 3;
			unsigned short EXENB : 1;
#endif
	} BIT;
	} CS1CR;
	char           wk15[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short RRCV : 4;
			unsigned short  : 4;
			unsigned short WRCV : 4;
			unsigned short  : 4;
#else
			unsigned short  : 4;
			unsigned short WRCV : 4;
			unsigned short  : 4;
			unsigned short RRCV : 4;
#endif
	} BIT;
	} CS1REC;
	char           wk16[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short EXENB : 1;
			unsigned short  : 3;
			unsigned short BSIZE : 2;
			unsigned short  : 2;
			unsigned short EMODE : 1;
			unsigned short  : 3;
			unsigned short MPXEN : 1;
			unsigned short  : 3;
#else
			unsigned short  : 3;
			unsigned short MPXEN : 1;
			unsigned short  : 3;
			unsigned short EMODE : 1;
			unsigned short  : 2;
			unsigned short BSIZE : 2;
			unsigned short  : 3;
			unsigned short EXENB : 1;
#endif
	} BIT;
	} CS2CR;
	char           wk17[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short RRCV : 4;
			unsigned short  : 4;
			unsigned short WRCV : 4;
			unsigned short  : 4;
#else
			unsigned short  : 4;
			unsigned short WRCV : 4;
			unsigned short  : 4;
			unsigned short RRCV : 4;
#endif
	} BIT;
	} CS2REC;
	char           wk18[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short EXENB : 1;
			unsigned short  : 3;
			unsigned short BSIZE : 2;
			unsigned short  : 2;
			unsigned short EMODE : 1;
			unsigned short  : 3;
			unsigned short MPXEN : 1;
			unsigned short  : 3;
#else
			unsigned short  : 3;
			unsigned short MPXEN : 1;
			unsigned short  : 3;
			unsigned short EMODE : 1;
			unsigned short  : 2;
			unsigned short BSIZE : 2;
			unsigned short  : 3;
			unsigned short EXENB : 1;
#endif
	} BIT;
	} CS3CR;
	char           wk19[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short RRCV : 4;
			unsigned short  : 4;
			unsigned short WRCV : 4;
			unsigned short  : 4;
#else
			unsigned short  : 4;
			unsigned short WRCV : 4;
			unsigned short  : 4;
			unsigned short RRCV : 4;
#endif
	} BIT;
	} CS3REC;
	char           wk20[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short EXENB : 1;
			unsigned short  : 3;
			unsigned short BSIZE : 2;
			unsigned short  : 2;
			unsigned short EMODE : 1;
			unsigned short  : 3;
			unsigned short MPXEN : 1;
			unsigned short  : 3;
#else
			unsigned short  : 3;
			unsigned short MPXEN : 1;
			unsigned short  : 3;
			unsigned short EMODE : 1;
			unsigned short  : 2;
			unsigned short BSIZE : 2;
			unsigned short  : 3;
			unsigned short EXENB : 1;
#endif
	} BIT;
	} CS4CR;
	char           wk21[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short RRCV : 4;
			unsigned short  : 4;
			unsigned short WRCV : 4;
			unsigned short  : 4;
#else
			unsigned short  : 4;
			unsigned short WRCV : 4;
			unsigned short  : 4;
			unsigned short RRCV : 4;
#endif
	} BIT;
	} CS4REC;
	char           wk22[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short EXENB : 1;
			unsigned short  : 3;
			unsigned short BSIZE : 2;
			unsigned short  : 2;
			unsigned short EMODE : 1;
			unsigned short  : 3;
			unsigned short MPXEN : 1;
			unsigned short  : 3;
#else
			unsigned short  : 3;
			unsigned short MPXEN : 1;
			unsigned short  : 3;
			unsigned short EMODE : 1;
			unsigned short  : 2;
			unsigned short BSIZE : 2;
			unsigned short  : 3;
			unsigned short EXENB : 1;
#endif
	} BIT;
	} CS5CR;
	char           wk23[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short RRCV : 4;
			unsigned short  : 4;
			unsigned short WRCV : 4;
			unsigned short  : 4;
#else
			unsigned short  : 4;
			unsigned short WRCV : 4;
			unsigned short  : 4;
			unsigned short RRCV : 4;
#endif
	} BIT;
	} CS5REC;
	char           wk24[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short EXENB : 1;
			unsigned short  : 3;
			unsigned short BSIZE : 2;
			unsigned short  : 2;
			unsigned short EMODE : 1;
			unsigned short  : 3;
			unsigned short MPXEN : 1;
			unsigned short  : 3;
#else
			unsigned short  : 3;
			unsigned short MPXEN : 1;
			unsigned short  : 3;
			unsigned short EMODE : 1;
			unsigned short  : 2;
			unsigned short BSIZE : 2;
			unsigned short  : 3;
			unsigned short EXENB : 1;
#endif
	} BIT;
	} CS6CR;
	char           wk25[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short RRCV : 4;
			unsigned short  : 4;
			unsigned short WRCV : 4;
			unsigned short  : 4;
#else
			unsigned short  : 4;
			unsigned short WRCV : 4;
			unsigned short  : 4;
			unsigned short RRCV : 4;
#endif
	} BIT;
	} CS6REC;
	char           wk26[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short EXENB : 1;
			unsigned short  : 3;
			unsigned short BSIZE : 2;
			unsigned short  : 2;
			unsigned short EMODE : 1;
			unsigned short  : 3;
			unsigned short MPXEN : 1;
			unsigned short  : 3;
#else
			unsigned short  : 3;
			unsigned short MPXEN : 1;
			unsigned short  : 3;
			unsigned short EMODE : 1;
			unsigned short  : 2;
			unsigned short BSIZE : 2;
			unsigned short  : 3;
			unsigned short EXENB : 1;
#endif
	} BIT;
	} CS7CR;
	char           wk27[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short RRCV : 4;
			unsigned short  : 4;
			unsigned short WRCV : 4;
			unsigned short  : 4;
#else
			unsigned short  : 4;
			unsigned short WRCV : 4;
			unsigned short  : 4;
			unsigned short RRCV : 4;
#endif
	} BIT;
	} CS7REC;
	char           wk28[4];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short RCVEN0 : 1;
			unsigned short RCVEN1 : 1;
			unsigned short RCVEN2 : 1;
			unsigned short RCVEN3 : 1;
			unsigned short RCVEN4 : 1;
			unsigned short RCVEN5 : 1;
			unsigned short RCVEN6 : 1;
			unsigned short RCVEN7 : 1;
			unsigned short RCVENM0 : 1;
			unsigned short RCVENM1 : 1;
			unsigned short RCVENM2 : 1;
			unsigned short RCVENM3 : 1;
			unsigned short RCVENM4 : 1;
			unsigned short RCVENM5 : 1;
			unsigned short RCVENM6 : 1;
			unsigned short RCVENM7 : 1;
#else
			unsigned short RCVENM7 : 1;
			unsigned short RCVENM6 : 1;
			unsigned short RCVENM5 : 1;
			unsigned short RCVENM4 : 1;
			unsigned short RCVENM3 : 1;
			unsigned short RCVENM2 : 1;
			unsigned short RCVENM1 : 1;
			unsigned short RCVENM0 : 1;
			unsigned short RCVEN7 : 1;
			unsigned short RCVEN6 : 1;
			unsigned short RCVEN5 : 1;
			unsigned short RCVEN4 : 1;
			unsigned short RCVEN3 : 1;
			unsigned short RCVEN2 : 1;
			unsigned short RCVEN1 : 1;
			unsigned short RCVEN0 : 1;
#endif
	} BIT;
	} CSRECEN;
	char           wk29[894];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char EXENB : 1;
			unsigned char  : 3;
			unsigned char BSIZE : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char BSIZE : 2;
			unsigned char  : 3;
			unsigned char EXENB : 1;
#endif
	} BIT;
	} SDCCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char EMODE : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char EMODE : 1;
#endif
	} BIT;
	} SDCMOD;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BE : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char BE : 1;
#endif
	} BIT;
	} SDAMOD;
	char           wk30[13];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SFEN : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char SFEN : 1;
#endif
	} BIT;
	} SDSELF;
	char           wk31[3];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short RFC : 12;
			unsigned short REFW : 4;
#else
			unsigned short REFW : 4;
			unsigned short RFC : 12;
#endif
	} BIT;
	} SDRFCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char RFEN : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char RFEN : 1;
#endif
	} BIT;
	} SDRFEN;
	char           wk32[9];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char INIRQ : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char INIRQ : 1;
#endif
	} BIT;
	} SDICR;
	char           wk33[3];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ARFI : 4;
			unsigned short ARFC : 4;
			unsigned short PRC : 3;
			unsigned short  : 5;
#else
			unsigned short  : 5;
			unsigned short PRC : 3;
			unsigned short ARFC : 4;
			unsigned short ARFI : 4;
#endif
	} BIT;
	} SDIR;
	char           wk34[26];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MXC : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char MXC : 2;
#endif
	} BIT;
	} SDADR;
	char           wk35[3];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CL : 3;
			unsigned long  : 5;
			unsigned long WR : 1;
			unsigned long RP : 3;
			unsigned long RCD : 2;
			unsigned long  : 2;
			unsigned long RAS : 3;
			unsigned long  : 13;
#else
			unsigned long  : 13;
			unsigned long RAS : 3;
			unsigned long  : 2;
			unsigned long RCD : 2;
			unsigned long RP : 3;
			unsigned long WR : 1;
			unsigned long  : 5;
			unsigned long CL : 3;
#endif
	} BIT;
	} SDTR;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short MR : 15;
			unsigned short  : 1;
#else
			unsigned short  : 1;
			unsigned short MR : 15;
#endif
	} BIT;
	} SDMOD;
	char           wk36[6];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MRSST : 1;
			unsigned char  : 2;
			unsigned char INIST : 1;
			unsigned char SRFST : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char SRFST : 1;
			unsigned char INIST : 1;
			unsigned char  : 2;
			unsigned char MRSST : 1;
#endif
	} BIT;
	} SDSR;
	char           wk37[269231];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PR1SEL : 3;
			unsigned long  : 1;
			unsigned long PR2SEL : 3;
			unsigned long  : 1;
			unsigned long PR3SEL : 3;
			unsigned long  : 1;
			unsigned long PR4SEL : 3;
			unsigned long  : 1;
			unsigned long PR5SEL : 3;
			unsigned long  : 12;
			unsigned long PRERR : 1;
#else
			unsigned long PRERR : 1;
			unsigned long  : 12;
			unsigned long PR5SEL : 3;
			unsigned long  : 1;
			unsigned long PR4SEL : 3;
			unsigned long  : 1;
			unsigned long PR3SEL : 3;
			unsigned long  : 1;
			unsigned long PR2SEL : 3;
			unsigned long  : 1;
			unsigned long PR1SEL : 3;
#endif
	} BIT;
	} EBMAPCR;
} st_bsc_t;

typedef struct st_cac {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CFME : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char CFME : 1;
#endif
	} BIT;
	} CACR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CACREFE : 1;
			unsigned char FMCS : 3;
			unsigned char TCSS : 2;
			unsigned char EDGES : 2;
#else
			unsigned char EDGES : 2;
			unsigned char TCSS : 2;
			unsigned char FMCS : 3;
			unsigned char CACREFE : 1;
#endif
	} BIT;
	} CACR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char RPS : 1;
			unsigned char RSCS : 3;
			unsigned char RCDS : 2;
			unsigned char DFS : 2;
#else
			unsigned char DFS : 2;
			unsigned char RCDS : 2;
			unsigned char RSCS : 3;
			unsigned char RPS : 1;
#endif
	} BIT;
	} CACR2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char FERRIE : 1;
			unsigned char MENDIE : 1;
			unsigned char OVFIE : 1;
			unsigned char  : 1;
			unsigned char FERRFCL : 1;
			unsigned char MENDFCL : 1;
			unsigned char OVFFCL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char OVFFCL : 1;
			unsigned char MENDFCL : 1;
			unsigned char FERRFCL : 1;
			unsigned char  : 1;
			unsigned char OVFIE : 1;
			unsigned char MENDIE : 1;
			unsigned char FERRIE : 1;
#endif
	} BIT;
	} CAICR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char FERRF : 1;
			unsigned char MENDF : 1;
			unsigned char OVFF : 1;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char OVFF : 1;
			unsigned char MENDF : 1;
			unsigned char FERRF : 1;
#endif
	} BIT;
	} CASTR;
	char           wk0[1];
	unsigned short CAULVR;
	unsigned short CALLVR;
	unsigned short CACNTBR;
} st_cac_t;

typedef struct st_can {
	struct {
		union {
			unsigned long LONG;
			struct {
				unsigned short H;
				unsigned short L;
			} WORD;
			struct {
				unsigned char HH;
				unsigned char HL;
				unsigned char LH;
				unsigned char LL;
			} BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EID : 18;
			unsigned long SID : 11;
			unsigned long  : 1;
			unsigned long RTR : 1;
			unsigned long IDE : 1;
#else
			unsigned long IDE : 1;
			unsigned long RTR : 1;
			unsigned long  : 1;
			unsigned long SID : 11;
			unsigned long EID : 18;
#endif
	} BIT;
		} ID;
		unsigned short DLC;
		unsigned char  DATA[8];
		unsigned short TS;
	} MB[32];
	union {
		unsigned long LONG;
		struct {
			unsigned short H;
			unsigned short L;
		} WORD;
		struct {
			unsigned char HH;
			unsigned char HL;
			unsigned char LH;
			unsigned char LL;
		} BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EID : 18;
			unsigned long SID : 11;
			unsigned long  : 3;
#else
			unsigned long  : 3;
			unsigned long SID : 11;
			unsigned long EID : 18;
#endif
	} BIT;
	} MKR[8];
	union {
		unsigned long LONG;
		struct {
			unsigned short H;
			unsigned short L;
		} WORD;
		struct {
			unsigned char HH;
			unsigned char HL;
			unsigned char LH;
			unsigned char LL;
		} BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EID : 18;
			unsigned long SID : 11;
			unsigned long  : 1;
			unsigned long RTR : 1;
			unsigned long IDE : 1;
#else
			unsigned long IDE : 1;
			unsigned long RTR : 1;
			unsigned long  : 1;
			unsigned long SID : 11;
			unsigned long EID : 18;
#endif
	} BIT;
	} FIDCR0;
	union {
		unsigned long LONG;
		struct {
			unsigned short H;
			unsigned short L;
		} WORD;
		struct {
			unsigned char HH;
			unsigned char HL;
			unsigned char LH;
			unsigned char LL;
		} BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EID : 18;
			unsigned long SID : 11;
			unsigned long  : 1;
			unsigned long RTR : 1;
			unsigned long IDE : 1;
#else
			unsigned long IDE : 1;
			unsigned long RTR : 1;
			unsigned long  : 1;
			unsigned long SID : 11;
			unsigned long EID : 18;
#endif
	} BIT;
	} FIDCR1;
	union {
		unsigned long LONG;
		struct {
			unsigned short H;
			unsigned short L;
		} WORD;
		struct {
			unsigned char HH;
			unsigned char HL;
			unsigned char LH;
			unsigned char LL;
		} BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MB0 : 1;
			unsigned long MB1 : 1;
			unsigned long MB2 : 1;
			unsigned long MB3 : 1;
			unsigned long MB4 : 1;
			unsigned long MB5 : 1;
			unsigned long MB6 : 1;
			unsigned long MB7 : 1;
			unsigned long MB8 : 1;
			unsigned long MB9 : 1;
			unsigned long MB10 : 1;
			unsigned long MB11 : 1;
			unsigned long MB12 : 1;
			unsigned long MB13 : 1;
			unsigned long MB14 : 1;
			unsigned long MB15 : 1;
			unsigned long MB16 : 1;
			unsigned long MB17 : 1;
			unsigned long MB18 : 1;
			unsigned long MB19 : 1;
			unsigned long MB20 : 1;
			unsigned long MB21 : 1;
			unsigned long MB22 : 1;
			unsigned long MB23 : 1;
			unsigned long MB24 : 1;
			unsigned long MB25 : 1;
			unsigned long MB26 : 1;
			unsigned long MB27 : 1;
			unsigned long MB28 : 1;
			unsigned long MB29 : 1;
			unsigned long MB30 : 1;
			unsigned long MB31 : 1;
#else
			unsigned long MB31 : 1;
			unsigned long MB30 : 1;
			unsigned long MB29 : 1;
			unsigned long MB28 : 1;
			unsigned long MB27 : 1;
			unsigned long MB26 : 1;
			unsigned long MB25 : 1;
			unsigned long MB24 : 1;
			unsigned long MB23 : 1;
			unsigned long MB22 : 1;
			unsigned long MB21 : 1;
			unsigned long MB20 : 1;
			unsigned long MB19 : 1;
			unsigned long MB18 : 1;
			unsigned long MB17 : 1;
			unsigned long MB16 : 1;
			unsigned long MB15 : 1;
			unsigned long MB14 : 1;
			unsigned long MB13 : 1;
			unsigned long MB12 : 1;
			unsigned long MB11 : 1;
			unsigned long MB10 : 1;
			unsigned long MB9 : 1;
			unsigned long MB8 : 1;
			unsigned long MB7 : 1;
			unsigned long MB6 : 1;
			unsigned long MB5 : 1;
			unsigned long MB4 : 1;
			unsigned long MB3 : 1;
			unsigned long MB2 : 1;
			unsigned long MB1 : 1;
			unsigned long MB0 : 1;
#endif
	} BIT;
	} MKIVLR;
	union {
		unsigned long LONG;
		struct {
			unsigned short H;
			unsigned short L;
		} WORD;
		struct {
			unsigned char HH;
			unsigned char HL;
			unsigned char LH;
			unsigned char LL;
		} BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MB0 : 1;
			unsigned long MB1 : 1;
			unsigned long MB2 : 1;
			unsigned long MB3 : 1;
			unsigned long MB4 : 1;
			unsigned long MB5 : 1;
			unsigned long MB6 : 1;
			unsigned long MB7 : 1;
			unsigned long MB8 : 1;
			unsigned long MB9 : 1;
			unsigned long MB10 : 1;
			unsigned long MB11 : 1;
			unsigned long MB12 : 1;
			unsigned long MB13 : 1;
			unsigned long MB14 : 1;
			unsigned long MB15 : 1;
			unsigned long MB16 : 1;
			unsigned long MB17 : 1;
			unsigned long MB18 : 1;
			unsigned long MB19 : 1;
			unsigned long MB20 : 1;
			unsigned long MB21 : 1;
			unsigned long MB22 : 1;
			unsigned long MB23 : 1;
			unsigned long MB24 : 1;
			unsigned long MB25 : 1;
			unsigned long MB26 : 1;
			unsigned long MB27 : 1;
			unsigned long MB28 : 1;
			unsigned long MB29 : 1;
			unsigned long MB30 : 1;
			unsigned long MB31 : 1;
#else
			unsigned long MB31 : 1;
			unsigned long MB30 : 1;
			unsigned long MB29 : 1;
			unsigned long MB28 : 1;
			unsigned long MB27 : 1;
			unsigned long MB26 : 1;
			unsigned long MB25 : 1;
			unsigned long MB24 : 1;
			unsigned long MB23 : 1;
			unsigned long MB22 : 1;
			unsigned long MB21 : 1;
			unsigned long MB20 : 1;
			unsigned long MB19 : 1;
			unsigned long MB18 : 1;
			unsigned long MB17 : 1;
			unsigned long MB16 : 1;
			unsigned long MB15 : 1;
			unsigned long MB14 : 1;
			unsigned long MB13 : 1;
			unsigned long MB12 : 1;
			unsigned long MB11 : 1;
			unsigned long MB10 : 1;
			unsigned long MB9 : 1;
			unsigned long MB8 : 1;
			unsigned long MB7 : 1;
			unsigned long MB6 : 1;
			unsigned long MB5 : 1;
			unsigned long MB4 : 1;
			unsigned long MB3 : 1;
			unsigned long MB2 : 1;
			unsigned long MB1 : 1;
			unsigned long MB0 : 1;
#endif
	} BIT;
	} MIER;
	char           wk0[1008];
	union {
		unsigned char BYTE;
		union {
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SENTDATA : 1;
			unsigned char TRMACTIVE : 1;
			unsigned char TRMABT : 1;
			unsigned char  : 1;
			unsigned char ONESHOT : 1;
			unsigned char  : 1;
			unsigned char RECREQ : 1;
			unsigned char TRMREQ : 1;
#else
			unsigned char TRMREQ : 1;
			unsigned char RECREQ : 1;
			unsigned char  : 1;
			unsigned char ONESHOT : 1;
			unsigned char  : 1;
			unsigned char TRMABT : 1;
			unsigned char TRMACTIVE : 1;
			unsigned char SENTDATA : 1;
#endif
	} TX;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NEWDATA : 1;
			unsigned char INVALDATA : 1;
			unsigned char MSGLOST : 1;
			unsigned char  : 1;
			unsigned char ONESHOT : 1;
			unsigned char  : 1;
			unsigned char RECREQ : 1;
			unsigned char TRMREQ : 1;
#else
			unsigned char TRMREQ : 1;
			unsigned char RECREQ : 1;
			unsigned char  : 1;
			unsigned char ONESHOT : 1;
			unsigned char  : 1;
			unsigned char MSGLOST : 1;
			unsigned char INVALDATA : 1;
			unsigned char NEWDATA : 1;
#endif
	} RX;
		} BIT;
	} MCTL[32];
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short MBM : 1;
			unsigned short IDFM : 2;
			unsigned short MLM : 1;
			unsigned short TPM : 1;
			unsigned short TSRC : 1;
			unsigned short TSPS : 2;
			unsigned short CANM : 2;
			unsigned short SLPM : 1;
			unsigned short BOM : 2;
			unsigned short RBOC : 1;
			unsigned short  : 2;
#else
			unsigned short  : 2;
			unsigned short RBOC : 1;
			unsigned short BOM : 2;
			unsigned short SLPM : 1;
			unsigned short CANM : 2;
			unsigned short TSPS : 2;
			unsigned short TSRC : 1;
			unsigned short TPM : 1;
			unsigned short MLM : 1;
			unsigned short IDFM : 2;
			unsigned short MBM : 1;
#endif
	} BIT;
	} CTLR;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short NDST : 1;
			unsigned short SDST : 1;
			unsigned short RFST : 1;
			unsigned short TFST : 1;
			unsigned short NMLST : 1;
			unsigned short FMLST : 1;
			unsigned short TABST : 1;
			unsigned short EST : 1;
			unsigned short RSTST : 1;
			unsigned short HLTST : 1;
			unsigned short SLPST : 1;
			unsigned short EPST : 1;
			unsigned short BOST : 1;
			unsigned short TRMST : 1;
			unsigned short RECST : 1;
			unsigned short  : 1;
#else
			unsigned short  : 1;
			unsigned short RECST : 1;
			unsigned short TRMST : 1;
			unsigned short BOST : 1;
			unsigned short EPST : 1;
			unsigned short SLPST : 1;
			unsigned short HLTST : 1;
			unsigned short RSTST : 1;
			unsigned short EST : 1;
			unsigned short TABST : 1;
			unsigned short FMLST : 1;
			unsigned short NMLST : 1;
			unsigned short TFST : 1;
			unsigned short RFST : 1;
			unsigned short SDST : 1;
			unsigned short NDST : 1;
#endif
	} BIT;
	} STR;
	union {
		unsigned long LONG;
		struct {
			unsigned short H;
			unsigned short L;
		} WORD;
		struct {
			unsigned char HH;
			unsigned char HL;
			unsigned char LH;
			unsigned char LL;
		} BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CCLKS : 1;
			unsigned long  : 7;
			unsigned long TSEG2 : 3;
			unsigned long  : 1;
			unsigned long SJW : 2;
			unsigned long  : 2;
			unsigned long BRP : 10;
			unsigned long  : 2;
			unsigned long TSEG1 : 4;
#else
			unsigned long TSEG1 : 4;
			unsigned long  : 2;
			unsigned long BRP : 10;
			unsigned long  : 2;
			unsigned long SJW : 2;
			unsigned long  : 1;
			unsigned long TSEG2 : 3;
			unsigned long  : 7;
			unsigned long CCLKS : 1;
#endif
	} BIT;
	} BCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char RFE : 1;
			unsigned char RFUST : 3;
			unsigned char RFMLF : 1;
			unsigned char RFFST : 1;
			unsigned char RFWST : 1;
			unsigned char RFEST : 1;
#else
			unsigned char RFEST : 1;
			unsigned char RFWST : 1;
			unsigned char RFFST : 1;
			unsigned char RFMLF : 1;
			unsigned char RFUST : 3;
			unsigned char RFE : 1;
#endif
	} BIT;
	} RFCR;
	unsigned char  RFPCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TFE : 1;
			unsigned char TFUST : 3;
			unsigned char  : 2;
			unsigned char TFFST : 1;
			unsigned char TFEST : 1;
#else
			unsigned char TFEST : 1;
			unsigned char TFFST : 1;
			unsigned char  : 2;
			unsigned char TFUST : 3;
			unsigned char TFE : 1;
#endif
	} BIT;
	} TFCR;
	unsigned char  TFPCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BEIE : 1;
			unsigned char EWIE : 1;
			unsigned char EPIE : 1;
			unsigned char BOEIE : 1;
			unsigned char BORIE : 1;
			unsigned char ORIE : 1;
			unsigned char OLIE : 1;
			unsigned char BLIE : 1;
#else
			unsigned char BLIE : 1;
			unsigned char OLIE : 1;
			unsigned char ORIE : 1;
			unsigned char BORIE : 1;
			unsigned char BOEIE : 1;
			unsigned char EPIE : 1;
			unsigned char EWIE : 1;
			unsigned char BEIE : 1;
#endif
	} BIT;
	} EIER;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BEIF : 1;
			unsigned char EWIF : 1;
			unsigned char EPIF : 1;
			unsigned char BOEIF : 1;
			unsigned char BORIF : 1;
			unsigned char ORIF : 1;
			unsigned char OLIF : 1;
			unsigned char BLIF : 1;
#else
			unsigned char BLIF : 1;
			unsigned char OLIF : 1;
			unsigned char ORIF : 1;
			unsigned char BORIF : 1;
			unsigned char BOEIF : 1;
			unsigned char EPIF : 1;
			unsigned char EWIF : 1;
			unsigned char BEIF : 1;
#endif
	} BIT;
	} EIFR;
	unsigned char  RECR;
	unsigned char  TECR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SEF : 1;
			unsigned char FEF : 1;
			unsigned char AEF : 1;
			unsigned char CEF : 1;
			unsigned char BE1F : 1;
			unsigned char BE0F : 1;
			unsigned char ADEF : 1;
			unsigned char EDPM : 1;
#else
			unsigned char EDPM : 1;
			unsigned char ADEF : 1;
			unsigned char BE0F : 1;
			unsigned char BE1F : 1;
			unsigned char CEF : 1;
			unsigned char AEF : 1;
			unsigned char FEF : 1;
			unsigned char SEF : 1;
#endif
	} BIT;
	} ECSR;
	unsigned char  CSSR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MBNST : 5;
			unsigned char  : 2;
			unsigned char SEST : 1;
#else
			unsigned char SEST : 1;
			unsigned char  : 2;
			unsigned char MBNST : 5;
#endif
	} BIT;
	} MSSR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MBSM : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char MBSM : 2;
#endif
	} BIT;
	} MSMR;
	unsigned short TSR;
	unsigned short AFSR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TSTE : 1;
			unsigned char TSTM : 2;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char TSTM : 2;
			unsigned char TSTE : 1;
#endif
	} BIT;
	} TCR;
} st_can_t;

typedef struct st_cmt {
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short STR0 : 1;
			unsigned short STR1 : 1;
			unsigned short  : 14;
#else
			unsigned short  : 14;
			unsigned short STR1 : 1;
			unsigned short STR0 : 1;
#endif
	} BIT;
	} CMSTR0;
	char           wk0[14];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short STR2 : 1;
			unsigned short STR3 : 1;
			unsigned short  : 14;
#else
			unsigned short  : 14;
			unsigned short STR3 : 1;
			unsigned short STR2 : 1;
#endif
	} BIT;
	} CMSTR1;
} st_cmt_t;

typedef struct st_cmt0 {
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CKS : 2;
			unsigned short  : 4;
			unsigned short CMIE : 1;
			unsigned short  : 9;
#else
			unsigned short  : 9;
			unsigned short CMIE : 1;
			unsigned short  : 4;
			unsigned short CKS : 2;
#endif
	} BIT;
	} CMCR;
	unsigned short CMCNT;
	unsigned short CMCOR;
} st_cmt0_t;

typedef struct st_cmtw {
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short STR : 1;
			unsigned short  : 15;
#else
			unsigned short  : 15;
			unsigned short STR : 1;
#endif
	} BIT;
	} CMWSTR;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CKS : 2;
			unsigned short  : 1;
			unsigned short CMWIE : 1;
			unsigned short IC0IE : 1;
			unsigned short IC1IE : 1;
			unsigned short OC0IE : 1;
			unsigned short OC1IE : 1;
			unsigned short  : 1;
			unsigned short CMS : 1;
			unsigned short  : 3;
			unsigned short CCLR : 3;
#else
			unsigned short CCLR : 3;
			unsigned short  : 3;
			unsigned short CMS : 1;
			unsigned short  : 1;
			unsigned short OC1IE : 1;
			unsigned short OC0IE : 1;
			unsigned short IC1IE : 1;
			unsigned short IC0IE : 1;
			unsigned short CMWIE : 1;
			unsigned short  : 1;
			unsigned short CKS : 2;
#endif
	} BIT;
	} CMWCR;
	char           wk1[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short IC0 : 2;
			unsigned short IC1 : 2;
			unsigned short IC0E : 1;
			unsigned short IC1E : 1;
			unsigned short  : 2;
			unsigned short OC0 : 2;
			unsigned short OC1 : 2;
			unsigned short OC0E : 1;
			unsigned short OC1E : 1;
			unsigned short  : 1;
			unsigned short CMWE : 1;
#else
			unsigned short CMWE : 1;
			unsigned short  : 1;
			unsigned short OC1E : 1;
			unsigned short OC0E : 1;
			unsigned short OC1 : 2;
			unsigned short OC0 : 2;
			unsigned short  : 2;
			unsigned short IC1E : 1;
			unsigned short IC0E : 1;
			unsigned short IC1 : 2;
			unsigned short IC0 : 2;
#endif
	} BIT;
	} CMWIOR;
	char           wk2[6];
	unsigned long  CMWCNT;
	unsigned long  CMWCOR;
	unsigned long  CMWICR0;
	unsigned long  CMWICR1;
	unsigned long  CMWOCR0;
	unsigned long  CMWOCR1;
} st_cmtw_t;

typedef struct st_crc {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char GPS : 3;
			unsigned char  : 3;
			unsigned char LMS : 1;
			unsigned char DORCLR : 1;
#else
			unsigned char DORCLR : 1;
			unsigned char LMS : 1;
			unsigned char  : 3;
			unsigned char GPS : 3;
#endif
	} BIT;
	} CRCCR;
	char           wk0[3];
	union {
		unsigned long LONG;
		unsigned char BYTE;
	} CRCDIR;
	union {
		unsigned long LONG;
		unsigned short WORD;
		unsigned char BYTE;
	} CRCDOR;
} st_crc_t;

typedef struct st_da {
	unsigned short DADR0;
	unsigned short DADR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 5;
			unsigned char DAE : 1;
			unsigned char DAOE0 : 1;
			unsigned char DAOE1 : 1;
#else
			unsigned char DAOE1 : 1;
			unsigned char DAOE0 : 1;
			unsigned char DAE : 1;
			unsigned char  : 5;
#endif
	} BIT;
	} DACR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 7;
			unsigned char DPSEL : 1;
#else
			unsigned char DPSEL : 1;
			unsigned char  : 7;
#endif
	} BIT;
	} DADPR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 7;
			unsigned char DAADST : 1;
#else
			unsigned char DAADST : 1;
			unsigned char  : 7;
#endif
	} BIT;
	} DAADSCR;
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 6;
			unsigned char DAAMP0 : 1;
			unsigned char DAAMP1 : 1;
#else
			unsigned char DAAMP1 : 1;
			unsigned char DAAMP0 : 1;
			unsigned char  : 6;
#endif
	} BIT;
	} DAAMPCR;
	char           wk1[19];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 6;
			unsigned char DAASW0 : 1;
			unsigned char DAASW1 : 1;
#else
			unsigned char DAASW1 : 1;
			unsigned char DAASW0 : 1;
			unsigned char  : 6;
#endif
	} BIT;
	} DAASWCR;
	char           wk2[17763];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 1;
			unsigned char AMADSEL1 : 1;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char AMADSEL1 : 1;
			unsigned char  : 1;
#endif
	} BIT;
	} DAADUSR;
} st_da_t;

typedef struct st_dmac {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DMST : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char DMST : 1;
#endif
	} BIT;
	} DMAST;
	char           wk0[3];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 4;
			unsigned char DMIS4 : 1;
			unsigned char DMIS5 : 1;
			unsigned char DMIS6 : 1;
			unsigned char DMIS7 : 1;
#else
			unsigned char DMIS7 : 1;
			unsigned char DMIS6 : 1;
			unsigned char DMIS5 : 1;
			unsigned char DMIS4 : 1;
			unsigned char  : 4;
#endif
	} BIT;
	} DMIST;
} st_dmac_t;

typedef struct st_dmac0 {
	void          *DMSAR;
	void          *DMDAR;
	unsigned long  DMCRA;
	unsigned short DMCRB;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short DCTG : 2;
			unsigned short  : 6;
			unsigned short SZ : 2;
			unsigned short  : 2;
			unsigned short DTS : 2;
			unsigned short MD : 2;
#else
			unsigned short MD : 2;
			unsigned short DTS : 2;
			unsigned short  : 2;
			unsigned short SZ : 2;
			unsigned short  : 6;
			unsigned short DCTG : 2;
#endif
	} BIT;
	} DMTMD;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DARIE : 1;
			unsigned char SARIE : 1;
			unsigned char RPTIE : 1;
			unsigned char ESIE : 1;
			unsigned char DTIE : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char DTIE : 1;
			unsigned char ESIE : 1;
			unsigned char RPTIE : 1;
			unsigned char SARIE : 1;
			unsigned char DARIE : 1;
#endif
	} BIT;
	} DMINT;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short DARA : 5;
			unsigned short  : 1;
			unsigned short DM : 2;
			unsigned short SARA : 5;
			unsigned short  : 1;
			unsigned short SM : 2;
#else
			unsigned short SM : 2;
			unsigned short  : 1;
			unsigned short SARA : 5;
			unsigned short DM : 2;
			unsigned short  : 1;
			unsigned short DARA : 5;
#endif
	} BIT;
	} DMAMD;
	char           wk2[2];
	unsigned long  DMOFR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DTE : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char DTE : 1;
#endif
	} BIT;
	} DMCNT;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SWREQ : 1;
			unsigned char  : 3;
			unsigned char CLRS : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char CLRS : 1;
			unsigned char  : 3;
			unsigned char SWREQ : 1;
#endif
	} BIT;
	} DMREQ;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ESIF : 1;
			unsigned char  : 3;
			unsigned char DTIF : 1;
			unsigned char  : 2;
			unsigned char ACT : 1;
#else
			unsigned char ACT : 1;
			unsigned char  : 2;
			unsigned char DTIF : 1;
			unsigned char  : 3;
			unsigned char ESIF : 1;
#endif
	} BIT;
	} DMSTS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DISEL : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char DISEL : 1;
#endif
	} BIT;
	} DMCSL;
} st_dmac0_t;

typedef struct st_dmac1 {
	void          *DMSAR;
	void          *DMDAR;
	unsigned long  DMCRA;
	unsigned short DMCRB;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short DCTG : 2;
			unsigned short  : 6;
			unsigned short SZ : 2;
			unsigned short  : 2;
			unsigned short DTS : 2;
			unsigned short MD : 2;
#else
			unsigned short MD : 2;
			unsigned short DTS : 2;
			unsigned short  : 2;
			unsigned short SZ : 2;
			unsigned short  : 6;
			unsigned short DCTG : 2;
#endif
	} BIT;
	} DMTMD;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DARIE : 1;
			unsigned char SARIE : 1;
			unsigned char RPTIE : 1;
			unsigned char ESIE : 1;
			unsigned char DTIE : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char DTIE : 1;
			unsigned char ESIE : 1;
			unsigned char RPTIE : 1;
			unsigned char SARIE : 1;
			unsigned char DARIE : 1;
#endif
	} BIT;
	} DMINT;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short DARA : 5;
			unsigned short  : 1;
			unsigned short DM : 2;
			unsigned short SARA : 5;
			unsigned short  : 1;
			unsigned short SM : 2;
#else
			unsigned short SM : 2;
			unsigned short  : 1;
			unsigned short SARA : 5;
			unsigned short DM : 2;
			unsigned short  : 1;
			unsigned short DARA : 5;
#endif
	} BIT;
	} DMAMD;
	char           wk2[6];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DTE : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char DTE : 1;
#endif
	} BIT;
	} DMCNT;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SWREQ : 1;
			unsigned char  : 3;
			unsigned char CLRS : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char CLRS : 1;
			unsigned char  : 3;
			unsigned char SWREQ : 1;
#endif
	} BIT;
	} DMREQ;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ESIF : 1;
			unsigned char  : 3;
			unsigned char DTIF : 1;
			unsigned char  : 2;
			unsigned char ACT : 1;
#else
			unsigned char ACT : 1;
			unsigned char  : 2;
			unsigned char DTIF : 1;
			unsigned char  : 3;
			unsigned char ESIF : 1;
#endif
	} BIT;
	} DMSTS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DISEL : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char DISEL : 1;
#endif
	} BIT;
	} DMCSL;
} st_dmac1_t;

typedef struct st_doc {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char OMS : 2;
			unsigned char DCSEL : 1;
			unsigned char  : 1;
			unsigned char DOPCIE : 1;
			unsigned char DOPCF : 1;
			unsigned char DOPCFCL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char DOPCFCL : 1;
			unsigned char DOPCF : 1;
			unsigned char DOPCIE : 1;
			unsigned char  : 1;
			unsigned char DCSEL : 1;
			unsigned char OMS : 2;
#endif
	} BIT;
	} DOCR;
	char           wk0[1];
	unsigned short DODIR;
	unsigned short DODSR;
} st_doc_t;

typedef struct st_drw2d {
	union {
		union {
			unsigned long LONG;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long LIM1EN : 1;
			unsigned long LIM2EN : 1;
			unsigned long LIM3EN : 1;
			unsigned long LIM4EN : 1;
			unsigned long LIM5EN : 1;
			unsigned long LIM6EN : 1;
			unsigned long QUAD1EN : 1;
			unsigned long QUAD2EN : 1;
			unsigned long QUAD3EN : 1;
			unsigned long LIM1TH : 1;
			unsigned long LIM2TH : 1;
			unsigned long LIM3TH : 1;
			unsigned long LIM4TH : 1;
			unsigned long LIM5TH : 1;
			unsigned long LIM6TH : 1;
			unsigned long BAND1EN : 1;
			unsigned long BAND2EN : 1;
			unsigned long UNION12 : 1;
			unsigned long UNION34 : 1;
			unsigned long UNION56 : 1;
			unsigned long UNIONAB : 1;
			unsigned long UNIONCD : 1;
			unsigned long SPANABT : 1;
			unsigned long SPANSTR : 1;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long SPANSTR : 1;
			unsigned long SPANABT : 1;
			unsigned long UNIONCD : 1;
			unsigned long UNIONAB : 1;
			unsigned long UNION56 : 1;
			unsigned long UNION34 : 1;
			unsigned long UNION12 : 1;
			unsigned long BAND2EN : 1;
			unsigned long BAND1EN : 1;
			unsigned long LIM6TH : 1;
			unsigned long LIM5TH : 1;
			unsigned long LIM4TH : 1;
			unsigned long LIM3TH : 1;
			unsigned long LIM2TH : 1;
			unsigned long LIM1TH : 1;
			unsigned long QUAD3EN : 1;
			unsigned long QUAD2EN : 1;
			unsigned long QUAD1EN : 1;
			unsigned long LIM6EN : 1;
			unsigned long LIM5EN : 1;
			unsigned long LIM4EN : 1;
			unsigned long LIM3EN : 1;
			unsigned long LIM2EN : 1;
			unsigned long LIM1EN : 1;
#endif
	} BIT;
		} CONTROL;
		union {
			unsigned long LONG;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long BSYENUM : 1;
			unsigned long BSYWR : 1;
			unsigned long CACHEDTY : 1;
			unsigned long DLSTACT : 1;
			unsigned long ENUIR : 1;
			unsigned long DLIR : 1;
			unsigned long  : 26;
#else
			unsigned long  : 26;
			unsigned long DLIR : 1;
			unsigned long ENUIR : 1;
			unsigned long DLSTACT : 1;
			unsigned long CACHEDTY : 1;
			unsigned long BSYWR : 1;
			unsigned long BSYENUM : 1;
#endif
	} BIT;
		} STATUS;
	};
	union {
		union {
			unsigned long LONG;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PTNEN : 1;
			unsigned long TEXENA : 1;
			unsigned long PTNSRCL5 : 1;
			unsigned long USEACB : 1;
			unsigned long RDFMT2 : 2;
			unsigned long BSFA : 1;
			unsigned long BDFA : 1;
			unsigned long WRFMT2 : 1;
			unsigned long BSF : 1;
			unsigned long BDF : 1;
			unsigned long BSI : 1;
			unsigned long BDI : 1;
			unsigned long BC2 : 1;
			unsigned long TEXCLPX : 1;
			unsigned long TEXCLPY : 1;
			unsigned long TEXFILTX : 1;
			unsigned long TEXFILTY : 1;
			unsigned long RDFMT : 2;
			unsigned long WRFMT : 2;
			unsigned long WRALPHA : 2;
			unsigned long RLEEN : 1;
			unsigned long CLUTEN : 1;
			unsigned long COLKEYEN : 1;
			unsigned long CLUTFORM : 1;
			unsigned long BSIA : 1;
			unsigned long BDIA : 1;
			unsigned long RLEPIXW : 2;
#else
			unsigned long RLEPIXW : 2;
			unsigned long BDIA : 1;
			unsigned long BSIA : 1;
			unsigned long CLUTFORM : 1;
			unsigned long COLKEYEN : 1;
			unsigned long CLUTEN : 1;
			unsigned long RLEEN : 1;
			unsigned long WRALPHA : 2;
			unsigned long WRFMT : 2;
			unsigned long RDFMT : 2;
			unsigned long TEXFILTY : 1;
			unsigned long TEXFILTX : 1;
			unsigned long TEXCLPY : 1;
			unsigned long TEXCLPX : 1;
			unsigned long BC2 : 1;
			unsigned long BDI : 1;
			unsigned long BSI : 1;
			unsigned long BDF : 1;
			unsigned long BSF : 1;
			unsigned long WRFMT2 : 1;
			unsigned long BDFA : 1;
			unsigned long BSFA : 1;
			unsigned long RDFMT2 : 2;
			unsigned long USEACB : 1;
			unsigned long PTNSRCL5 : 1;
			unsigned long TEXENA : 1;
			unsigned long PTNEN : 1;
#endif
	} BIT;
		} CONTROL2;
		union {
			unsigned long LONG;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long REV : 12;
			unsigned long  : 5;
			unsigned long DLR : 1;
			unsigned long FBCACHE : 1;
			unsigned long TXCACHE : 1;
			unsigned long PERFCNT : 1;
			unsigned long TEXCLUT : 1;
			unsigned long  : 1;
			unsigned long RLEUNIT : 1;
			unsigned long TEXCLUT256 : 1;
			unsigned long COLKEY : 1;
			unsigned long  : 1;
			unsigned long ACBLD : 1;
			unsigned long  : 4;
#else
			unsigned long  : 4;
			unsigned long ACBLD : 1;
			unsigned long  : 1;
			unsigned long COLKEY : 1;
			unsigned long TEXCLUT256 : 1;
			unsigned long RLEUNIT : 1;
			unsigned long  : 1;
			unsigned long TEXCLUT : 1;
			unsigned long PERFCNT : 1;
			unsigned long TXCACHE : 1;
			unsigned long FBCACHE : 1;
			unsigned long DLR : 1;
			unsigned long  : 5;
			unsigned long REV : 12;
#endif
	} BIT;
		} HWVER;
	};
	char           wk0[8];
	unsigned long  L1START;
	unsigned long  L2START;
	unsigned long  L3START;
	unsigned long  L4START;
	unsigned long  L5START;
	unsigned long  L6START;
	unsigned long  L1XADD;
	unsigned long  L2XADD;
	unsigned long  L3XADD;
	unsigned long  L4XADD;
	unsigned long  L5XADD;
	unsigned long  L6XADD;
	unsigned long  L1YADD;
	unsigned long  L2YADD;
	unsigned long  L3YADD;
	unsigned long  L4YADD;
	unsigned long  L5YADD;
	unsigned long  L6YADD;
	unsigned long  L1BAND;
	unsigned long  L2BAND;
	char           wk1[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long COL1B : 8;
			unsigned long COL1G : 8;
			unsigned long COL1R : 8;
			unsigned long COL1A : 8;
#else
			unsigned long COL1A : 8;
			unsigned long COL1R : 8;
			unsigned long COL1G : 8;
			unsigned long COL1B : 8;
#endif
	} BIT;
	} COLOR1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long COL2B : 8;
			unsigned long COL2G : 8;
			unsigned long COL2R : 8;
			unsigned long COL2A : 8;
#else
			unsigned long COL2A : 8;
			unsigned long COL2R : 8;
			unsigned long COL2G : 8;
			unsigned long COL2B : 8;
#endif
	} BIT;
	} COLOR2;
	char           wk2[8];
	unsigned long  PATTERN;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long X : 16;
			unsigned long Y : 16;
#else
			unsigned long Y : 16;
			unsigned long X : 16;
#endif
	} BIT;
	} SIZE;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PITCH : 16;
			unsigned long SSD : 16;
#else
			unsigned long SSD : 16;
			unsigned long PITCH : 16;
#endif
	} BIT;
	} PITCH;
	unsigned long  ORIGIN;
	char           wk3[12];
	unsigned long  LUST;
	unsigned long  LUXADD;
	unsigned long  LUYADD;
	unsigned long  LVSTI;
	unsigned long  LVSTF;
	unsigned long  LVXADDI;
	unsigned long  LVYADDI;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long LVXADDF : 16;
			unsigned long LVYADDF : 16;
#else
			unsigned long LVYADDF : 16;
			unsigned long LVXADDF : 16;
#endif
	} BIT;
	} LVYXADDF;
	char           wk4[4];
	unsigned long  TEXPITCH;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TEXUMSK : 11;
			unsigned long TEXVMSK : 21;
#else
			unsigned long TEXVMSK : 21;
			unsigned long TEXUMSK : 11;
#endif
	} BIT;
	} TEXMSK;
	unsigned long  TEXORG;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ENUIREN : 1;
			unsigned long DLIREN : 1;
			unsigned long ENUIRCLR : 1;
			unsigned long DLIRCLR : 1;
			unsigned long  : 28;
#else
			unsigned long  : 28;
			unsigned long DLIRCLR : 1;
			unsigned long ENUIRCLR : 1;
			unsigned long DLIREN : 1;
			unsigned long ENUIREN : 1;
#endif
	} BIT;
	} IRQCTL;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CENFX : 1;
			unsigned long CFLUFX : 1;
			unsigned long CENTX : 1;
			unsigned long CFLUTX : 1;
			unsigned long  : 28;
#else
			unsigned long  : 28;
			unsigned long CFLUTX : 1;
			unsigned long CENTX : 1;
			unsigned long CFLUFX : 1;
			unsigned long CENFX : 1;
#endif
	} BIT;
	} CACHECTL;
	unsigned long  DLISTST;
	unsigned long  PERFCNT1;
	unsigned long  PERFCNT2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TRG1 : 16;
			unsigned long TRG2 : 16;
#else
			unsigned long TRG2 : 16;
			unsigned long TRG1 : 16;
#endif
	} BIT;
	} PERFTRG;
	char           wk5[4];
	unsigned long  TEXCLADDR;
	unsigned long  TEXCLDATA;
	unsigned long  TEXCLOFST;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long B : 8;
			unsigned long G : 8;
			unsigned long R : 8;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long R : 8;
			unsigned long G : 8;
			unsigned long B : 8;
#endif
	} BIT;
	} COLKEY;
} st_drw2d_t;

typedef struct st_dtc {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 4;
			unsigned char RRS : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char RRS : 1;
			unsigned char  : 4;
#endif
	} BIT;
	} DTCCR;
	char           wk0[3];
	void          *DTCVBR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SHORT : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char SHORT : 1;
#endif
	} BIT;
	} DTCADMOD;
	char           wk1[3];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DTCST : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char DTCST : 1;
#endif
	} BIT;
	} DTCST;
	char           wk2[1];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short VECN : 8;
			unsigned short  : 7;
			unsigned short ACT : 1;
#else
			unsigned short ACT : 1;
			unsigned short  : 7;
			unsigned short VECN : 8;
#endif
	} BIT;
	} DTCSTS;
	void          *DTCIBR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SQTFRL : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char SQTFRL : 1;
#endif
	} BIT;
	} DTCOR;
	char           wk3[1];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short VECN : 8;
			unsigned short  : 7;
			unsigned short ESPSEL : 1;
#else
			unsigned short ESPSEL : 1;
			unsigned short  : 7;
			unsigned short VECN : 8;
#endif
	} BIT;
	} DTCSQE;
	unsigned long  DTCDISP;
} st_dtc_t;

typedef struct st_eccram {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char RAMMOD : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char RAMMOD : 2;
#endif
	} BIT;
	} ECCRAMMODE;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ECC2ERR : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char ECC2ERR : 1;
#endif
	} BIT;
	} ECCRAM2STS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ECC1STSEN : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char ECC1STSEN : 1;
#endif
	} BIT;
	} ECCRAM1STSEN;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ECC1ERR : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char ECC1ERR : 1;
#endif
	} BIT;
	} ECCRAM1STS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PRCR : 1;
			unsigned char KW : 7;
#else
			unsigned char KW : 7;
			unsigned char PRCR : 1;
#endif
	} BIT;
	} ECCRAMPRCR;
	char           wk0[3];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 3;
			unsigned long ECC2EAD : 12;
			unsigned long  : 17;
#else
			unsigned long  : 17;
			unsigned long ECC2EAD : 12;
			unsigned long  : 3;
#endif
	} BIT;
	} ECCRAM2ECAD;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 3;
			unsigned long ECC1EAD : 12;
			unsigned long  : 17;
#else
			unsigned long  : 17;
			unsigned long ECC1EAD : 12;
			unsigned long  : 3;
#endif
	} BIT;
	} ECCRAM1ECAD;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PRCR2 : 1;
			unsigned char KW2 : 7;
#else
			unsigned char KW2 : 7;
			unsigned char PRCR2 : 1;
#endif
	} BIT;
	} ECCRAMPRCR2;
	char           wk1[3];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TSTBYP : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char TSTBYP : 1;
#endif
	} BIT;
	} ECCRAMETST;
} st_eccram_t;

typedef struct st_edmac {
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long SWR : 1;
			unsigned long  : 3;
			unsigned long DL : 2;
			unsigned long DE : 1;
			unsigned long  : 25;
#else
			unsigned long  : 25;
			unsigned long DE : 1;
			unsigned long DL : 2;
			unsigned long  : 3;
			unsigned long SWR : 1;
#endif
	} BIT;
	} EDMR;
	char           wk0[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TR : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long TR : 1;
#endif
	} BIT;
	} EDTRR;
	char           wk1[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RR : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long RR : 1;
#endif
	} BIT;
	} EDRRR;
	char           wk2[4];
	void          *TDLAR;
	char           wk3[4];
	void          *RDLAR;
	char           wk4[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CERF : 1;
			unsigned long PRE : 1;
			unsigned long RTSF : 1;
			unsigned long RTLF : 1;
			unsigned long RRF : 1;
			unsigned long  : 2;
			unsigned long RMAF : 1;
			unsigned long TRO : 1;
			unsigned long CD : 1;
			unsigned long DLC : 1;
			unsigned long CND : 1;
			unsigned long  : 4;
			unsigned long RFOF : 1;
			unsigned long RDE : 1;
			unsigned long FR : 1;
			unsigned long TFUF : 1;
			unsigned long TDE : 1;
			unsigned long TC : 1;
			unsigned long ECI : 1;
			unsigned long  : 1;
			unsigned long RFCOF : 1;
			unsigned long RABT : 1;
			unsigned long TABT : 1;
			unsigned long  : 3;
			unsigned long TWB : 1;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long TWB : 1;
			unsigned long  : 3;
			unsigned long TABT : 1;
			unsigned long RABT : 1;
			unsigned long RFCOF : 1;
			unsigned long  : 1;
			unsigned long ECI : 1;
			unsigned long TC : 1;
			unsigned long TDE : 1;
			unsigned long TFUF : 1;
			unsigned long FR : 1;
			unsigned long RDE : 1;
			unsigned long RFOF : 1;
			unsigned long  : 4;
			unsigned long CND : 1;
			unsigned long DLC : 1;
			unsigned long CD : 1;
			unsigned long TRO : 1;
			unsigned long RMAF : 1;
			unsigned long  : 2;
			unsigned long RRF : 1;
			unsigned long RTLF : 1;
			unsigned long RTSF : 1;
			unsigned long PRE : 1;
			unsigned long CERF : 1;
#endif
	} BIT;
	} EESR;
	char           wk5[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CERFIP : 1;
			unsigned long PREIP : 1;
			unsigned long RTSFIP : 1;
			unsigned long RTLFIP : 1;
			unsigned long RRFIP : 1;
			unsigned long  : 2;
			unsigned long RMAFIP : 1;
			unsigned long TROIP : 1;
			unsigned long CDIP : 1;
			unsigned long DLCIP : 1;
			unsigned long CNDIP : 1;
			unsigned long  : 4;
			unsigned long RFOFIP : 1;
			unsigned long RDEIP : 1;
			unsigned long FRIP : 1;
			unsigned long TFUFIP : 1;
			unsigned long TDEIP : 1;
			unsigned long TCIP : 1;
			unsigned long ECIIP : 1;
			unsigned long  : 1;
			unsigned long RFCOFIP : 1;
			unsigned long RABTIP : 1;
			unsigned long TABTIP : 1;
			unsigned long  : 3;
			unsigned long TWBIP : 1;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long TWBIP : 1;
			unsigned long  : 3;
			unsigned long TABTIP : 1;
			unsigned long RABTIP : 1;
			unsigned long RFCOFIP : 1;
			unsigned long  : 1;
			unsigned long ECIIP : 1;
			unsigned long TCIP : 1;
			unsigned long TDEIP : 1;
			unsigned long TFUFIP : 1;
			unsigned long FRIP : 1;
			unsigned long RDEIP : 1;
			unsigned long RFOFIP : 1;
			unsigned long  : 4;
			unsigned long CNDIP : 1;
			unsigned long DLCIP : 1;
			unsigned long CDIP : 1;
			unsigned long TROIP : 1;
			unsigned long RMAFIP : 1;
			unsigned long  : 2;
			unsigned long RRFIP : 1;
			unsigned long RTLFIP : 1;
			unsigned long RTSFIP : 1;
			unsigned long PREIP : 1;
			unsigned long CERFIP : 1;
#endif
	} BIT;
	} EESIPR;
	char           wk6[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 4;
			unsigned long RRFCE : 1;
			unsigned long  : 2;
			unsigned long RMAFCE : 1;
			unsigned long  : 24;
#else
			unsigned long  : 24;
			unsigned long RMAFCE : 1;
			unsigned long  : 2;
			unsigned long RRFCE : 1;
			unsigned long  : 4;
#endif
	} BIT;
	} TRSCER;
	char           wk7[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MFC : 16;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long MFC : 16;
#endif
	} BIT;
	} RMFCR;
	char           wk8[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TFT : 11;
			unsigned long  : 21;
#else
			unsigned long  : 21;
			unsigned long TFT : 11;
#endif
	} BIT;
	} TFTR;
	char           wk9[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RFD : 5;
			unsigned long  : 3;
			unsigned long TFD : 5;
			unsigned long  : 19;
#else
			unsigned long  : 19;
			unsigned long TFD : 5;
			unsigned long  : 3;
			unsigned long RFD : 5;
#endif
	} BIT;
	} FDR;
	char           wk10[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RNR : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long RNR : 1;
#endif
	} BIT;
	} RMCR;
	char           wk11[8];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long UNDER : 16;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long UNDER : 16;
#endif
	} BIT;
	} TFUCR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long OVER : 16;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long OVER : 16;
#endif
	} BIT;
	} RFOCR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ELB : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long ELB : 1;
#endif
	} BIT;
	} IOSR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RFDO : 3;
			unsigned long  : 13;
			unsigned long RFFO : 3;
			unsigned long  : 13;
#else
			unsigned long  : 13;
			unsigned long RFFO : 3;
			unsigned long  : 13;
			unsigned long RFDO : 3;
#endif
	} BIT;
	} FCFTR;
	char           wk12[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PADR : 6;
			unsigned long  : 10;
			unsigned long PADS : 2;
			unsigned long  : 14;
#else
			unsigned long  : 14;
			unsigned long PADS : 2;
			unsigned long  : 10;
			unsigned long PADR : 6;
#endif
	} BIT;
	} RPADIR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TIS : 1;
			unsigned long  : 3;
			unsigned long TIM : 1;
			unsigned long  : 27;
#else
			unsigned long  : 27;
			unsigned long TIM : 1;
			unsigned long  : 3;
			unsigned long TIS : 1;
#endif
	} BIT;
	} TRIMD;
	char           wk13[72];
	void          *RBWAR;
	void          *RDFAR;
	char           wk14[4];
	void          *TBRAR;
	void          *TDFAR;
} st_edmac_t;

typedef struct st_elc {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 7;
			unsigned char ELCON : 1;
#else
			unsigned char ELCON : 1;
			unsigned char  : 7;
#endif
	} BIT;
	} ELCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR0;
	char           wk0[2];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR3;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR4;
	char           wk1[2];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR7;
	char           wk2[2];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR10;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR11;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR12;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR13;
	char           wk3[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR15;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR16;
	char           wk4[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR18;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR19;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR20;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR21;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR22;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR23;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR24;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR25;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR26;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR27;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR28;
	char           wk5[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MTU0MD : 2;
			unsigned char  : 4;
			unsigned char MTU3MD : 2;
#else
			unsigned char MTU3MD : 2;
			unsigned char  : 4;
			unsigned char MTU0MD : 2;
#endif
	} BIT;
	} ELOPA;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MTU4MD : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char MTU4MD : 2;
#endif
	} BIT;
	} ELOPB;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 2;
			unsigned char CMT1MD : 2;
			unsigned char  : 4;
#else
			unsigned char  : 4;
			unsigned char CMT1MD : 2;
			unsigned char  : 2;
#endif
	} BIT;
	} ELOPC;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TMR0MD : 2;
			unsigned char TMR1MD : 2;
			unsigned char TMR2MD : 2;
			unsigned char TMR3MD : 2;
#else
			unsigned char TMR3MD : 2;
			unsigned char TMR2MD : 2;
			unsigned char TMR1MD : 2;
			unsigned char TMR0MD : 2;
#endif
	} BIT;
	} ELOPD;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PGR0 : 1;
			unsigned char PGR1 : 1;
			unsigned char PGR2 : 1;
			unsigned char PGR3 : 1;
			unsigned char PGR4 : 1;
			unsigned char PGR5 : 1;
			unsigned char PGR6 : 1;
			unsigned char PGR7 : 1;
#else
			unsigned char PGR7 : 1;
			unsigned char PGR6 : 1;
			unsigned char PGR5 : 1;
			unsigned char PGR4 : 1;
			unsigned char PGR3 : 1;
			unsigned char PGR2 : 1;
			unsigned char PGR1 : 1;
			unsigned char PGR0 : 1;
#endif
	} BIT;
	} PGR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PGR0 : 1;
			unsigned char PGR1 : 1;
			unsigned char PGR2 : 1;
			unsigned char PGR3 : 1;
			unsigned char PGR4 : 1;
			unsigned char PGR5 : 1;
			unsigned char PGR6 : 1;
			unsigned char PGR7 : 1;
#else
			unsigned char PGR7 : 1;
			unsigned char PGR6 : 1;
			unsigned char PGR5 : 1;
			unsigned char PGR4 : 1;
			unsigned char PGR3 : 1;
			unsigned char PGR2 : 1;
			unsigned char PGR1 : 1;
			unsigned char PGR0 : 1;
#endif
	} BIT;
	} PGR2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PGCI : 2;
			unsigned char PGCOVE : 1;
			unsigned char  : 1;
			unsigned char PGCO : 3;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char PGCO : 3;
			unsigned char  : 1;
			unsigned char PGCOVE : 1;
			unsigned char PGCI : 2;
#endif
	} BIT;
	} PGC1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PGCI : 2;
			unsigned char PGCOVE : 1;
			unsigned char  : 1;
			unsigned char PGCO : 3;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char PGCO : 3;
			unsigned char  : 1;
			unsigned char PGCOVE : 1;
			unsigned char PGCI : 2;
#endif
	} BIT;
	} PGC2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PDBF0 : 1;
			unsigned char PDBF1 : 1;
			unsigned char PDBF2 : 1;
			unsigned char PDBF3 : 1;
			unsigned char PDBF4 : 1;
			unsigned char PDBF5 : 1;
			unsigned char PDBF6 : 1;
			unsigned char PDBF7 : 1;
#else
			unsigned char PDBF7 : 1;
			unsigned char PDBF6 : 1;
			unsigned char PDBF5 : 1;
			unsigned char PDBF4 : 1;
			unsigned char PDBF3 : 1;
			unsigned char PDBF2 : 1;
			unsigned char PDBF1 : 1;
			unsigned char PDBF0 : 1;
#endif
	} BIT;
	} PDBF1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PDBF0 : 1;
			unsigned char PDBF1 : 1;
			unsigned char PDBF2 : 1;
			unsigned char PDBF3 : 1;
			unsigned char PDBF4 : 1;
			unsigned char PDBF5 : 1;
			unsigned char PDBF6 : 1;
			unsigned char PDBF7 : 1;
#else
			unsigned char PDBF7 : 1;
			unsigned char PDBF6 : 1;
			unsigned char PDBF5 : 1;
			unsigned char PDBF4 : 1;
			unsigned char PDBF3 : 1;
			unsigned char PDBF2 : 1;
			unsigned char PDBF1 : 1;
			unsigned char PDBF0 : 1;
#endif
	} BIT;
	} PDBF2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSB : 3;
			unsigned char PSP : 2;
			unsigned char PSM : 2;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char PSM : 2;
			unsigned char PSP : 2;
			unsigned char PSB : 3;
#endif
	} BIT;
	} PEL0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSB : 3;
			unsigned char PSP : 2;
			unsigned char PSM : 2;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char PSM : 2;
			unsigned char PSP : 2;
			unsigned char PSB : 3;
#endif
	} BIT;
	} PEL1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSB : 3;
			unsigned char PSP : 2;
			unsigned char PSM : 2;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char PSM : 2;
			unsigned char PSP : 2;
			unsigned char PSB : 3;
#endif
	} BIT;
	} PEL2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSB : 3;
			unsigned char PSP : 2;
			unsigned char PSM : 2;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char PSM : 2;
			unsigned char PSP : 2;
			unsigned char PSB : 3;
#endif
	} BIT;
	} PEL3;
	union {
		unsigned char BYTE;
#ifdef IODEFINE_H_HISTORY
		struct {
			unsigned char WI:1;
			unsigned char WE:1;
			unsigned char :5;
			unsigned char SEG:1;
		} BIT;
#endif
	} ELSEGR;
	char           wk6[3];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR33;
	char           wk7[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR35;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR36;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR37;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR38;
	char           wk8[6];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR45;
	char           wk9[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPU0MD : 2;
			unsigned char TPU1MD : 2;
			unsigned char TPU2MD : 2;
			unsigned char TPU3MD : 2;
#else
			unsigned char TPU3MD : 2;
			unsigned char TPU2MD : 2;
			unsigned char TPU1MD : 2;
			unsigned char TPU0MD : 2;
#endif
	} BIT;
	} ELOPF;
	char           wk10[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CMTW0MD : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char CMTW0MD : 2;
#endif
	} BIT;
	} ELOPH;
	char           wk11[4];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR48;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR49;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR50;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR51;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR52;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR53;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR54;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR55;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR56;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ELS : 8;
#else
			unsigned char ELS : 8;
#endif
	} BIT;
	} ELSR57;
} st_elc_t;

typedef struct st_eptpc {
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RESET : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long RESET : 1;
#endif
	} BIT;
	} PTRSTR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long SCLKDIV : 3;
			unsigned long  : 5;
			unsigned long SCLKSEL : 3;
			unsigned long  : 21;
#else
			unsigned long  : 21;
			unsigned long SCLKSEL : 3;
			unsigned long  : 5;
			unsigned long SCLKDIV : 3;
#endif
	} BIT;
	} STCSELR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long BYPASS0 : 1;
			unsigned long  : 15;
			unsigned long BYPASS1 : 1;
			unsigned long  : 15;
#else
			unsigned long  : 15;
			unsigned long BYPASS1 : 1;
			unsigned long  : 15;
			unsigned long BYPASS0 : 1;
#endif
	} BIT;
	} SYBYPSR;
	char           wk0[15092];
	unsigned long  MIESR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ST : 1;
			unsigned long SY0 : 1;
			unsigned long SY1 : 1;
			unsigned long PR : 1;
			unsigned long  : 12;
			unsigned long CYC0 : 1;
			unsigned long CYC1 : 1;
			unsigned long CYC2 : 1;
			unsigned long CYC3 : 1;
			unsigned long CYC4 : 1;
			unsigned long CYC5 : 1;
			unsigned long  : 10;
#else
			unsigned long  : 10;
			unsigned long CYC5 : 1;
			unsigned long CYC4 : 1;
			unsigned long CYC3 : 1;
			unsigned long CYC2 : 1;
			unsigned long CYC1 : 1;
			unsigned long CYC0 : 1;
			unsigned long  : 12;
			unsigned long PR : 1;
			unsigned long SY1 : 1;
			unsigned long SY0 : 1;
			unsigned long ST : 1;
#endif
	} BIT;
	} MIEIPR;
	char           wk1[8];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CYCP0 : 1;
			unsigned long CYCP1 : 1;
			unsigned long CYCP2 : 1;
			unsigned long CYCP3 : 1;
			unsigned long CYCP4 : 1;
			unsigned long CYCP5 : 1;
			unsigned long  : 2;
			unsigned long CYCN0 : 1;
			unsigned long CYCN1 : 1;
			unsigned long CYCN2 : 1;
			unsigned long CYCN3 : 1;
			unsigned long CYCN4 : 1;
			unsigned long CYCN5 : 1;
			unsigned long  : 2;
			unsigned long PLSP : 1;
			unsigned long  : 7;
			unsigned long PLSN : 1;
			unsigned long  : 7;
#else
			unsigned long  : 7;
			unsigned long PLSN : 1;
			unsigned long  : 7;
			unsigned long PLSP : 1;
			unsigned long  : 2;
			unsigned long CYCN5 : 1;
			unsigned long CYCN4 : 1;
			unsigned long CYCN3 : 1;
			unsigned long CYCN2 : 1;
			unsigned long CYCN1 : 1;
			unsigned long CYCN0 : 1;
			unsigned long  : 2;
			unsigned long CYCP5 : 1;
			unsigned long CYCP4 : 1;
			unsigned long CYCP3 : 1;
			unsigned long CYCP2 : 1;
			unsigned long CYCP1 : 1;
			unsigned long CYCP0 : 1;
#endif
	} BIT;
	} ELIPPR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CYCP0 : 1;
			unsigned long CYCP1 : 1;
			unsigned long CYCP2 : 1;
			unsigned long CYCP3 : 1;
			unsigned long CYCP4 : 1;
			unsigned long CYCP5 : 1;
			unsigned long  : 2;
			unsigned long CYCN0 : 1;
			unsigned long CYCN1 : 1;
			unsigned long CYCN2 : 1;
			unsigned long CYCN3 : 1;
			unsigned long CYCN4 : 1;
			unsigned long CYCN5 : 1;
			unsigned long  : 2;
			unsigned long PLSP : 1;
			unsigned long  : 7;
			unsigned long PLSN : 1;
			unsigned long  : 7;
#else
			unsigned long  : 7;
			unsigned long PLSN : 1;
			unsigned long  : 7;
			unsigned long PLSP : 1;
			unsigned long  : 2;
			unsigned long CYCN5 : 1;
			unsigned long CYCN4 : 1;
			unsigned long CYCN3 : 1;
			unsigned long CYCN2 : 1;
			unsigned long CYCN1 : 1;
			unsigned long CYCN0 : 1;
			unsigned long  : 2;
			unsigned long CYCP5 : 1;
			unsigned long CYCP4 : 1;
			unsigned long CYCP3 : 1;
			unsigned long CYCP2 : 1;
			unsigned long CYCP1 : 1;
			unsigned long CYCP0 : 1;
#endif
	} BIT;
	} ELIPACR;
	char           wk2[40];
	unsigned long  STSR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long SYNC : 1;
			unsigned long SYNCOUT : 1;
			unsigned long  : 1;
			unsigned long SYNTOUT : 1;
			unsigned long W10D : 1;
			unsigned long  : 27;
#else
			unsigned long  : 27;
			unsigned long W10D : 1;
			unsigned long SYNTOUT : 1;
			unsigned long  : 1;
			unsigned long SYNCOUT : 1;
			unsigned long SYNC : 1;
#endif
	} BIT;
	} STIPR;
	char           wk3[8];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long STCF : 2;
			unsigned long  : 30;
#else
			unsigned long  : 30;
			unsigned long STCF : 2;
#endif
	} BIT;
	} STCFR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long WINT : 8;
			unsigned long  : 5;
			unsigned long CMOD : 1;
			unsigned long  : 1;
			unsigned long W10S : 1;
			unsigned long SYTH : 4;
			unsigned long DVTH : 4;
			unsigned long  : 4;
			unsigned long ALEN0 : 1;
			unsigned long ALEN1 : 1;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long ALEN1 : 1;
			unsigned long ALEN0 : 1;
			unsigned long  : 4;
			unsigned long DVTH : 4;
			unsigned long SYTH : 4;
			unsigned long W10S : 1;
			unsigned long  : 1;
			unsigned long CMOD : 1;
			unsigned long  : 5;
			unsigned long WINT : 8;
#endif
	} BIT;
	} STMR;
	unsigned long  SYNTOR;
	char           wk4[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long IPTSEL0 : 1;
			unsigned long IPTSEL1 : 1;
			unsigned long IPTSEL2 : 1;
			unsigned long IPTSEL3 : 1;
			unsigned long IPTSEL4 : 1;
			unsigned long IPTSEL5 : 1;
			unsigned long  : 26;
#else
			unsigned long  : 26;
			unsigned long IPTSEL5 : 1;
			unsigned long IPTSEL4 : 1;
			unsigned long IPTSEL3 : 1;
			unsigned long IPTSEL2 : 1;
			unsigned long IPTSEL1 : 1;
			unsigned long IPTSEL0 : 1;
#endif
	} BIT;
	} IPTSELR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MINTEN0 : 1;
			unsigned long MINTEN1 : 1;
			unsigned long MINTEN2 : 1;
			unsigned long MINTEN3 : 1;
			unsigned long MINTEN4 : 1;
			unsigned long MINTEN5 : 1;
			unsigned long  : 26;
#else
			unsigned long  : 26;
			unsigned long MINTEN5 : 1;
			unsigned long MINTEN4 : 1;
			unsigned long MINTEN3 : 1;
			unsigned long MINTEN2 : 1;
			unsigned long MINTEN1 : 1;
			unsigned long MINTEN0 : 1;
#endif
	} BIT;
	} MITSELR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ELTDIS0 : 1;
			unsigned long ELTDIS1 : 1;
			unsigned long ELTDIS2 : 1;
			unsigned long ELTDIS3 : 1;
			unsigned long ELTDIS4 : 1;
			unsigned long ELTDIS5 : 1;
			unsigned long  : 26;
#else
			unsigned long  : 26;
			unsigned long ELTDIS5 : 1;
			unsigned long ELTDIS4 : 1;
			unsigned long ELTDIS3 : 1;
			unsigned long ELTDIS2 : 1;
			unsigned long ELTDIS1 : 1;
			unsigned long ELTDIS0 : 1;
#endif
	} BIT;
	} ELTSELR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long SYSEL : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long SYSEL : 1;
#endif
	} BIT;
	} STCHSELR;
	char           wk5[16];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long STR : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long STR : 1;
#endif
	} BIT;
	} SYNSTARTR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long LOAD : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long LOAD : 1;
#endif
	} BIT;
	} LCIVLDR;
	char           wk6[8];
	unsigned long  SYNTDARU;
	unsigned long  SYNTDARL;
	unsigned long  SYNTDBRU;
	unsigned long  SYNTDBRL;
	char           wk7[16];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long VALU : 16;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long VALU : 16;
#endif
	} BIT;
	} LCIVRU;
	unsigned long  LCIVRM;
	unsigned long  LCIVRL;
	char           wk8[104];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GW10 : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long GW10 : 1;
#endif
	} BIT;
	} GETW10R;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long LMTU : 31;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long LMTU : 31;
#endif
	} BIT;
	} PLIMITRU;
	unsigned long  PLIMITRM;
	unsigned long  PLIMITRL;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long LMTU : 31;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long LMTU : 31;
#endif
	} BIT;
	} MLIMITRU;
	unsigned long  MLIMITRM;
	unsigned long  MLIMITRL;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long INFO : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long INFO : 1;
#endif
	} BIT;
	} GETINFOR;
	char           wk9[44];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CNTU : 16;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long CNTU : 16;
#endif
	} BIT;
	} LCCVRU;
	unsigned long  LCCVRM;
	unsigned long  LCCVRL;
	char           wk10[148];
	unsigned long  PW10VRU;
	unsigned long  PW10VRM;
	unsigned long  PW10VRL;
	char           wk11[180];
	unsigned long  MW10RU;
	unsigned long  MW10RM;
	unsigned long  MW10RL;
	char           wk12[36];
	unsigned long  TMSTTRU0;
	unsigned long  TMSTTRL0;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CYC : 30;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long CYC : 30;
#endif
	} BIT;
	} TMCYCR0;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long WTH : 29;
			unsigned long  : 3;
#else
			unsigned long  : 3;
			unsigned long WTH : 29;
#endif
	} BIT;
	} TMPLSR0;
	unsigned long  TMSTTRU1;
	unsigned long  TMSTTRL1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CYC : 30;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long CYC : 30;
#endif
	} BIT;
	} TMCYCR1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long WTH : 29;
			unsigned long  : 3;
#else
			unsigned long  : 3;
			unsigned long WTH : 29;
#endif
	} BIT;
	} TMPLSR1;
	unsigned long  TMSTTRU2;
	unsigned long  TMSTTRL2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CYC : 30;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long CYC : 30;
#endif
	} BIT;
	} TMCYCR2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long WTH : 29;
			unsigned long  : 3;
#else
			unsigned long  : 3;
			unsigned long WTH : 29;
#endif
	} BIT;
	} TMPLSR2;
	unsigned long  TMSTTRU3;
	unsigned long  TMSTTRL3;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CYC : 30;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long CYC : 30;
#endif
	} BIT;
	} TMCYCR3;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long WTH : 29;
			unsigned long  : 3;
#else
			unsigned long  : 3;
			unsigned long WTH : 29;
#endif
	} BIT;
	} TMPLSR3;
	unsigned long  TMSTTRU4;
	unsigned long  TMSTTRL4;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CYC : 30;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long CYC : 30;
#endif
	} BIT;
	} TMCYCR4;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long WTH : 29;
			unsigned long  : 3;
#else
			unsigned long  : 3;
			unsigned long WTH : 29;
#endif
	} BIT;
	} TMPLSR4;
	unsigned long  TMSTTRU5;
	unsigned long  TMSTTRL5;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CYC : 30;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long CYC : 30;
#endif
	} BIT;
	} TMCYCR5;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long WTH : 29;
			unsigned long  : 3;
#else
			unsigned long  : 3;
			unsigned long WTH : 29;
#endif
	} BIT;
	} TMPLSR5;
	char           wk13[28];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EN0 : 1;
			unsigned long EN1 : 1;
			unsigned long EN2 : 1;
			unsigned long EN3 : 1;
			unsigned long EN4 : 1;
			unsigned long EN5 : 1;
			unsigned long  : 26;
#else
			unsigned long  : 26;
			unsigned long EN5 : 1;
			unsigned long EN4 : 1;
			unsigned long EN3 : 1;
			unsigned long EN2 : 1;
			unsigned long EN1 : 1;
			unsigned long EN0 : 1;
#endif
	} BIT;
	} TMSTARTR;
	char           wk14[128];
	unsigned long  PRSR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long OVRE0 : 1;
			unsigned long OVRE1 : 1;
			unsigned long OVRE2 : 1;
			unsigned long OVRE3 : 1;
			unsigned long  : 4;
			unsigned long MACE : 1;
			unsigned long  : 19;
			unsigned long URE0 : 1;
			unsigned long URE1 : 1;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long URE1 : 1;
			unsigned long URE0 : 1;
			unsigned long  : 19;
			unsigned long MACE : 1;
			unsigned long  : 4;
			unsigned long OVRE3 : 1;
			unsigned long OVRE2 : 1;
			unsigned long OVRE1 : 1;
			unsigned long OVRE0 : 1;
#endif
	} BIT;
	} PRIPR;
	char           wk15[8];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MACU : 24;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long MACU : 24;
#endif
	} BIT;
	} PRMACRU0;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MACL : 24;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long MACL : 24;
#endif
	} BIT;
	} PRMACRL0;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MACU : 24;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long MACU : 24;
#endif
	} BIT;
	} PRMACRU1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MACL : 24;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long MACL : 24;
#endif
	} BIT;
	} PRMACRL1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TDIS : 2;
			unsigned long  : 30;
#else
			unsigned long  : 30;
			unsigned long TDIS : 2;
#endif
	} BIT;
	} TRNDISR;
	char           wk16[12];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MOD : 1;
			unsigned long  : 7;
			unsigned long FWD0 : 1;
			unsigned long FWD1 : 1;
			unsigned long  : 22;
#else
			unsigned long  : 22;
			unsigned long FWD1 : 1;
			unsigned long FWD0 : 1;
			unsigned long  : 7;
			unsigned long MOD : 1;
#endif
	} BIT;
	} TRNMR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long THVAL : 11;
			unsigned long  : 21;
#else
			unsigned long  : 21;
			unsigned long THVAL : 11;
#endif
	} BIT;
	} TRNCTTDR;
} st_eptpc_t;

typedef struct st_eptpc0 {
	unsigned long  SYSR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long OFMUD : 1;
			unsigned long INTCHG : 1;
			unsigned long MPDUD : 1;
			unsigned long  : 1;
			unsigned long DRPTO : 1;
			unsigned long INTDEV : 1;
			unsigned long DRQOVR : 1;
			unsigned long  : 5;
			unsigned long RECLP : 1;
			unsigned long  : 1;
			unsigned long INFABT : 1;
			unsigned long  : 1;
			unsigned long RESDN : 1;
			unsigned long GENDN : 1;
			unsigned long  : 14;
#else
			unsigned long  : 14;
			unsigned long GENDN : 1;
			unsigned long RESDN : 1;
			unsigned long  : 1;
			unsigned long INFABT : 1;
			unsigned long  : 1;
			unsigned long RECLP : 1;
			unsigned long  : 5;
			unsigned long DRQOVR : 1;
			unsigned long INTDEV : 1;
			unsigned long DRPTO : 1;
			unsigned long  : 1;
			unsigned long MPDUD : 1;
			unsigned long INTCHG : 1;
			unsigned long OFMUD : 1;
#endif
	} BIT;
	} SYIPR;
	char           wk0[8];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MACU : 24;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long MACU : 24;
#endif
	} BIT;
	} SYMACRU;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MACL : 24;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long MACL : 24;
#endif
	} BIT;
	} SYMACRL;
	unsigned long  SYLLCCTLR;
	unsigned long  SYIPADDRR;
	char           wk1[32];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long VER : 4;
			unsigned long TRSP : 4;
			unsigned long  : 24;
#else
			unsigned long  : 24;
			unsigned long TRSP : 4;
			unsigned long VER : 4;
#endif
	} BIT;
	} SYSPVRR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long DNUM : 8;
			unsigned long  : 24;
#else
			unsigned long  : 24;
			unsigned long DNUM : 8;
#endif
	} BIT;
	} SYDOMR;
	char           wk2[8];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long FLAG0 : 1;
			unsigned long FLAG1 : 1;
			unsigned long FLAG2 : 1;
			unsigned long FLAG3 : 1;
			unsigned long FLAG4 : 1;
			unsigned long FLAG5 : 1;
			unsigned long  : 2;
			unsigned long FLAG8 : 1;
			unsigned long  : 1;
			unsigned long FLAG10 : 1;
			unsigned long  : 2;
			unsigned long FLAG13 : 1;
			unsigned long FLAG14 : 1;
			unsigned long  : 17;
#else
			unsigned long  : 17;
			unsigned long FLAG14 : 1;
			unsigned long FLAG13 : 1;
			unsigned long  : 2;
			unsigned long FLAG10 : 1;
			unsigned long  : 1;
			unsigned long FLAG8 : 1;
			unsigned long  : 2;
			unsigned long FLAG5 : 1;
			unsigned long FLAG4 : 1;
			unsigned long FLAG3 : 1;
			unsigned long FLAG2 : 1;
			unsigned long FLAG1 : 1;
			unsigned long FLAG0 : 1;
#endif
	} BIT;
	} ANFR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 8;
			unsigned long FLAG8 : 1;
			unsigned long FLAG9 : 1;
			unsigned long FLAG10 : 1;
			unsigned long  : 2;
			unsigned long FLAG13 : 1;
			unsigned long FLAG14 : 1;
			unsigned long  : 17;
#else
			unsigned long  : 17;
			unsigned long FLAG14 : 1;
			unsigned long FLAG13 : 1;
			unsigned long  : 2;
			unsigned long FLAG10 : 1;
			unsigned long FLAG9 : 1;
			unsigned long FLAG8 : 1;
			unsigned long  : 8;
#endif
	} BIT;
	} SYNFR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 10;
			unsigned long FLAG10 : 1;
			unsigned long  : 2;
			unsigned long FLAG13 : 1;
			unsigned long FLAG14 : 1;
			unsigned long  : 17;
#else
			unsigned long  : 17;
			unsigned long FLAG14 : 1;
			unsigned long FLAG13 : 1;
			unsigned long  : 2;
			unsigned long FLAG10 : 1;
			unsigned long  : 10;
#endif
	} BIT;
	} DYRQFR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 8;
			unsigned long FLAG8 : 1;
			unsigned long FLAG9 : 1;
			unsigned long FLAG10 : 1;
			unsigned long  : 2;
			unsigned long FLAG13 : 1;
			unsigned long FLAG14 : 1;
			unsigned long  : 17;
#else
			unsigned long  : 17;
			unsigned long FLAG14 : 1;
			unsigned long FLAG13 : 1;
			unsigned long  : 2;
			unsigned long FLAG10 : 1;
			unsigned long FLAG9 : 1;
			unsigned long FLAG8 : 1;
			unsigned long  : 8;
#endif
	} BIT;
	} DYRPFR;
	unsigned long  SYCIDRU;
	unsigned long  SYCIDRL;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PNUM : 16;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long PNUM : 16;
#endif
	} BIT;
	} SYPNUMR;
	char           wk3[20];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long BMUP : 1;
			unsigned long STUP : 1;
			unsigned long ANUP : 1;
			unsigned long  : 29;
#else
			unsigned long  : 29;
			unsigned long ANUP : 1;
			unsigned long STUP : 1;
			unsigned long BMUP : 1;
#endif
	} BIT;
	} SYRVLDR;
	char           wk4[12];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ANCE : 2;
			unsigned long  : 2;
			unsigned long SYNC : 3;
			unsigned long  : 1;
			unsigned long FUP : 3;
			unsigned long  : 1;
			unsigned long DRQ : 3;
			unsigned long  : 1;
			unsigned long DRP : 3;
			unsigned long  : 1;
			unsigned long PDRQ : 3;
			unsigned long  : 1;
			unsigned long PDRP : 3;
			unsigned long  : 1;
			unsigned long PDFUP : 3;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long PDFUP : 3;
			unsigned long  : 1;
			unsigned long PDRP : 3;
			unsigned long  : 1;
			unsigned long PDRQ : 3;
			unsigned long  : 1;
			unsigned long DRP : 3;
			unsigned long  : 1;
			unsigned long DRQ : 3;
			unsigned long  : 1;
			unsigned long FUP : 3;
			unsigned long  : 1;
			unsigned long SYNC : 3;
			unsigned long  : 2;
			unsigned long ANCE : 2;
#endif
	} BIT;
	} SYRFL1R;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MAN : 2;
			unsigned long  : 2;
			unsigned long SIG : 2;
			unsigned long  : 22;
			unsigned long ILL : 2;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long ILL : 2;
			unsigned long  : 22;
			unsigned long SIG : 2;
			unsigned long  : 2;
			unsigned long MAN : 2;
#endif
	} BIT;
	} SYRFL2R;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ANCE : 1;
			unsigned long  : 3;
			unsigned long SYNC : 1;
			unsigned long  : 3;
			unsigned long DRQ : 1;
			unsigned long  : 3;
			unsigned long PDRQ : 1;
			unsigned long  : 19;
#else
			unsigned long  : 19;
			unsigned long PDRQ : 1;
			unsigned long  : 3;
			unsigned long DRQ : 1;
			unsigned long  : 3;
			unsigned long SYNC : 1;
			unsigned long  : 3;
			unsigned long ANCE : 1;
#endif
	} BIT;
	} SYTRENR;
	char           wk5[4];
	unsigned long  MTCIDU;
	unsigned long  MTCIDL;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PNUM : 16;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long PNUM : 16;
#endif
	} BIT;
	} MTPID;
	char           wk6[20];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ANCE : 8;
			unsigned long SYNC : 8;
			unsigned long DREQ : 8;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long DREQ : 8;
			unsigned long SYNC : 8;
			unsigned long ANCE : 8;
#endif
	} BIT;
	} SYTLIR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ANCE : 8;
			unsigned long SYNC : 8;
			unsigned long DRESP : 8;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long DRESP : 8;
			unsigned long SYNC : 8;
			unsigned long ANCE : 8;
#endif
	} BIT;
	} SYRLIR;
	unsigned long  OFMRU;
	unsigned long  OFMRL;
	unsigned long  MPDRU;
	unsigned long  MPDRL;
	char           wk7[8];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GMPR2 : 8;
			unsigned long  : 8;
			unsigned long GMPR1 : 8;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long GMPR1 : 8;
			unsigned long  : 8;
			unsigned long GMPR2 : 8;
#endif
	} BIT;
	} GMPR;
	unsigned long  GMCQR;
	unsigned long  GMIDRU;
	unsigned long  GMIDRL;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TSRC : 8;
			unsigned long  : 8;
			unsigned long CUTO : 16;
#else
			unsigned long CUTO : 16;
			unsigned long  : 8;
			unsigned long TSRC : 8;
#endif
	} BIT;
	} CUOTSR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long SRMV : 16;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long SRMV : 16;
#endif
	} BIT;
	} SRR;
	char           wk8[8];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MACU : 24;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long MACU : 24;
#endif
	} BIT;
	} PPMACRU;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MACL : 24;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long MACL : 24;
#endif
	} BIT;
	} PPMACRL;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MACU : 24;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long MACU : 24;
#endif
	} BIT;
	} PDMACRU;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MACL : 24;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long MACL : 24;
#endif
	} BIT;
	} PDMACRL;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TYPE : 16;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long TYPE : 16;
#endif
	} BIT;
	} PETYPER;
	char           wk9[12];
	unsigned long  PPIPR;
	unsigned long  PDIPR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EVTO : 8;
			unsigned long  : 24;
#else
			unsigned long  : 24;
			unsigned long EVTO : 8;
#endif
	} BIT;
	} PETOSR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GETO : 8;
			unsigned long  : 24;
#else
			unsigned long  : 24;
			unsigned long GETO : 8;
#endif
	} BIT;
	} PGTOSR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PRTL : 8;
			unsigned long  : 24;
#else
			unsigned long  : 24;
			unsigned long PRTL : 8;
#endif
	} BIT;
	} PPTTLR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PDTL : 8;
			unsigned long  : 24;
#else
			unsigned long  : 24;
			unsigned long PDTL : 8;
#endif
	} BIT;
	} PDTTLR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EVUPT : 16;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long EVUPT : 16;
#endif
	} BIT;
	} PEUDPR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GEUPT : 16;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long GEUPT : 16;
#endif
	} BIT;
	} PGUDPR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long SEL : 1;
			unsigned long PRT : 1;
			unsigned long ENB : 1;
			unsigned long  : 13;
			unsigned long EXTPRM : 1;
			unsigned long  : 15;
#else
			unsigned long  : 15;
			unsigned long EXTPRM : 1;
			unsigned long  : 13;
			unsigned long ENB : 1;
			unsigned long PRT : 1;
			unsigned long SEL : 1;
#endif
	} BIT;
	} FFLTR;
	char           wk10[28];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MACU : 24;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long MACU : 24;
#endif
	} BIT;
	} FMAC0RU;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MACL : 24;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long MACL : 24;
#endif
	} BIT;
	} FMAC0RL;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MACU : 24;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long MACU : 24;
#endif
	} BIT;
	} FMAC1RU;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MACL : 24;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long MACL : 24;
#endif
	} BIT;
	} FMAC1RL;
	char           wk11[80];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ASYMU : 16;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long ASYMU : 16;
#endif
	} BIT;
	} DASYMRU;
	unsigned long  DASYMRL;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EGP : 16;
			unsigned long INGP : 16;
#else
			unsigned long INGP : 16;
			unsigned long EGP : 16;
#endif
	} BIT;
	} TSLATR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TCYC : 8;
			unsigned long  : 4;
			unsigned long SBDIS : 1;
			unsigned long  : 3;
			unsigned long FILDIS : 1;
			unsigned long  : 3;
			unsigned long TCMOD : 1;
			unsigned long  : 11;
#else
			unsigned long  : 11;
			unsigned long TCMOD : 1;
			unsigned long  : 3;
			unsigned long FILDIS : 1;
			unsigned long  : 3;
			unsigned long SBDIS : 1;
			unsigned long  : 4;
			unsigned long TCYC : 8;
#endif
	} BIT;
	} SYCONFR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long FORM0 : 1;
			unsigned long FORM1 : 1;
			unsigned long  : 30;
#else
			unsigned long  : 30;
			unsigned long FORM1 : 1;
			unsigned long FORM0 : 1;
#endif
	} BIT;
	} SYFORMR;
	unsigned long  RSTOUTR;
} st_eptpc0_t;

typedef struct st_etherc {
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PRM : 1;
			unsigned long DM : 1;
			unsigned long RTM : 1;
			unsigned long ILB : 1;
			unsigned long  : 1;
			unsigned long TE : 1;
			unsigned long RE : 1;
			unsigned long  : 2;
			unsigned long MPDE : 1;
			unsigned long  : 2;
			unsigned long PRCEF : 1;
			unsigned long  : 3;
			unsigned long TXF : 1;
			unsigned long RXF : 1;
			unsigned long PFR : 1;
			unsigned long ZPF : 1;
			unsigned long TPC : 1;
			unsigned long  : 11;
#else
			unsigned long  : 11;
			unsigned long TPC : 1;
			unsigned long ZPF : 1;
			unsigned long PFR : 1;
			unsigned long RXF : 1;
			unsigned long TXF : 1;
			unsigned long  : 3;
			unsigned long PRCEF : 1;
			unsigned long  : 2;
			unsigned long MPDE : 1;
			unsigned long  : 2;
			unsigned long RE : 1;
			unsigned long TE : 1;
			unsigned long  : 1;
			unsigned long ILB : 1;
			unsigned long RTM : 1;
			unsigned long DM : 1;
			unsigned long PRM : 1;
#endif
	} BIT;
	} ECMR;
	char           wk0[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RFL : 12;
			unsigned long  : 20;
#else
			unsigned long  : 20;
			unsigned long RFL : 12;
#endif
	} BIT;
	} RFLR;
	char           wk1[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ICD : 1;
			unsigned long MPD : 1;
			unsigned long LCHNG : 1;
			unsigned long  : 1;
			unsigned long PSRTO : 1;
			unsigned long BFR : 1;
			unsigned long  : 26;
#else
			unsigned long  : 26;
			unsigned long BFR : 1;
			unsigned long PSRTO : 1;
			unsigned long  : 1;
			unsigned long LCHNG : 1;
			unsigned long MPD : 1;
			unsigned long ICD : 1;
#endif
	} BIT;
	} ECSR;
	char           wk2[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ICDIP : 1;
			unsigned long MPDIP : 1;
			unsigned long LCHNGIP : 1;
			unsigned long  : 1;
			unsigned long PSRTOIP : 1;
			unsigned long BFSIPR : 1;
			unsigned long  : 26;
#else
			unsigned long  : 26;
			unsigned long BFSIPR : 1;
			unsigned long PSRTOIP : 1;
			unsigned long  : 1;
			unsigned long LCHNGIP : 1;
			unsigned long MPDIP : 1;
			unsigned long ICDIP : 1;
#endif
	} BIT;
	} ECSIPR;
	char           wk3[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MDC : 1;
			unsigned long MMD : 1;
			unsigned long MDO : 1;
			unsigned long MDI : 1;
			unsigned long  : 28;
#else
			unsigned long  : 28;
			unsigned long MDI : 1;
			unsigned long MDO : 1;
			unsigned long MMD : 1;
			unsigned long MDC : 1;
#endif
	} BIT;
	} PIR;
	char           wk4[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long LMON : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long LMON : 1;
#endif
	} BIT;
	} PSR;
	char           wk5[20];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RMD : 20;
			unsigned long  : 12;
#else
			unsigned long  : 12;
			unsigned long RMD : 20;
#endif
	} BIT;
	} RDMLR;
	char           wk6[12];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long IPG : 5;
			unsigned long  : 27;
#else
			unsigned long  : 27;
			unsigned long IPG : 5;
#endif
	} BIT;
	} IPGR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long AP : 16;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long AP : 16;
#endif
	} BIT;
	} APR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MP : 16;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long MP : 16;
#endif
	} BIT;
	} MPR;
	char           wk7[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RPAUSE : 8;
			unsigned long  : 24;
#else
			unsigned long  : 24;
			unsigned long RPAUSE : 8;
#endif
	} BIT;
	} RFCF;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TPAUSE : 16;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long TPAUSE : 16;
#endif
	} BIT;
	} TPAUSER;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TXP : 8;
			unsigned long  : 24;
#else
			unsigned long  : 24;
			unsigned long TXP : 8;
#endif
	} BIT;
	} TPAUSECR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long BCF : 16;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long BCF : 16;
#endif
	} BIT;
	} BCFRR;
	char           wk8[80];
	unsigned long  MAHR;
	char           wk9[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MA : 16;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long MA : 16;
#endif
	} BIT;
	} MALR;
	char           wk10[4];
	unsigned long  TROCR;
	unsigned long  CDCR;
	unsigned long  LCCR;
	unsigned long  CNDCR;
	char           wk11[4];
	unsigned long  CEFCR;
	unsigned long  FRECR;
	unsigned long  TSFRCR;
	unsigned long  TLFRCR;
	unsigned long  RFCR;
	unsigned long  MAFCR;
} st_etherc_t;

typedef struct st_exdmac {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DMST : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char DMST : 1;
#endif
	} BIT;
	} EDMAST;
	char           wk0[479];
	unsigned long  CLSBR0;
	unsigned long  CLSBR1;
	unsigned long  CLSBR2;
	unsigned long  CLSBR3;
	unsigned long  CLSBR4;
	unsigned long  CLSBR5;
	unsigned long  CLSBR6;
	unsigned long  CLSBR7;
} st_exdmac_t;

typedef struct st_exdmac0 {
	void          *EDMSAR;
	void          *EDMDAR;
	unsigned long  EDMCRA;
	unsigned short EDMCRB;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short DCTG : 2;
			unsigned short  : 6;
			unsigned short SZ : 2;
			unsigned short  : 2;
			unsigned short DTS : 2;
			unsigned short MD : 2;
#else
			unsigned short MD : 2;
			unsigned short DTS : 2;
			unsigned short  : 2;
			unsigned short SZ : 2;
			unsigned short  : 6;
			unsigned short DCTG : 2;
#endif
	} BIT;
	} EDMTMD;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DACKSEL : 1;
			unsigned char DACKW : 1;
			unsigned char DACKE : 1;
			unsigned char DACKS : 1;
			unsigned char  : 4;
#else
			unsigned char  : 4;
			unsigned char DACKS : 1;
			unsigned char DACKE : 1;
			unsigned char DACKW : 1;
			unsigned char DACKSEL : 1;
#endif
	} BIT;
	} EDMOMD;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DARIE : 1;
			unsigned char SARIE : 1;
			unsigned char RPTIE : 1;
			unsigned char ESIE : 1;
			unsigned char DTIE : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char DTIE : 1;
			unsigned char ESIE : 1;
			unsigned char RPTIE : 1;
			unsigned char SARIE : 1;
			unsigned char DARIE : 1;
#endif
	} BIT;
	} EDMINT;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long DARA : 5;
			unsigned long  : 1;
			unsigned long DM : 2;
			unsigned long SARA : 5;
			unsigned long  : 1;
			unsigned long SM : 2;
			unsigned long DIR : 1;
			unsigned long AMS : 1;
			unsigned long  : 14;
#else
			unsigned long  : 14;
			unsigned long AMS : 1;
			unsigned long DIR : 1;
			unsigned long SM : 2;
			unsigned long  : 1;
			unsigned long SARA : 5;
			unsigned long DM : 2;
			unsigned long  : 1;
			unsigned long DARA : 5;
#endif
	} BIT;
	} EDMAMD;
	unsigned long  EDMOFR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DTE : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char DTE : 1;
#endif
	} BIT;
	} EDMCNT;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SWREQ : 1;
			unsigned char  : 3;
			unsigned char CLRS : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char CLRS : 1;
			unsigned char  : 3;
			unsigned char SWREQ : 1;
#endif
	} BIT;
	} EDMREQ;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ESIF : 1;
			unsigned char  : 3;
			unsigned char DTIF : 1;
			unsigned char  : 2;
			unsigned char ACT : 1;
#else
			unsigned char ACT : 1;
			unsigned char  : 2;
			unsigned char DTIF : 1;
			unsigned char  : 3;
			unsigned char ESIF : 1;
#endif
	} BIT;
	} EDMSTS;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DREQS : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char DREQS : 2;
#endif
	} BIT;
	} EDMRMD;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char EREQ : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char EREQ : 1;
#endif
	} BIT;
	} EDMERF;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PREQ : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char PREQ : 1;
#endif
	} BIT;
	} EDMPRF;
} st_exdmac0_t;

typedef struct st_exdmac1 {
	void          *EDMSAR;
	void          *EDMDAR;
	unsigned long  EDMCRA;
	unsigned short EDMCRB;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short DCTG : 2;
			unsigned short  : 6;
			unsigned short SZ : 2;
			unsigned short  : 2;
			unsigned short DTS : 2;
			unsigned short MD : 2;
#else
			unsigned short MD : 2;
			unsigned short DTS : 2;
			unsigned short  : 2;
			unsigned short SZ : 2;
			unsigned short  : 6;
			unsigned short DCTG : 2;
#endif
	} BIT;
	} EDMTMD;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DACKSEL : 1;
			unsigned char DACKW : 1;
			unsigned char DACKE : 1;
			unsigned char DACKS : 1;
			unsigned char  : 4;
#else
			unsigned char  : 4;
			unsigned char DACKS : 1;
			unsigned char DACKE : 1;
			unsigned char DACKW : 1;
			unsigned char DACKSEL : 1;
#endif
	} BIT;
	} EDMOMD;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DARIE : 1;
			unsigned char SARIE : 1;
			unsigned char RPTIE : 1;
			unsigned char ESIE : 1;
			unsigned char DTIE : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char DTIE : 1;
			unsigned char ESIE : 1;
			unsigned char RPTIE : 1;
			unsigned char SARIE : 1;
			unsigned char DARIE : 1;
#endif
	} BIT;
	} EDMINT;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long DARA : 5;
			unsigned long  : 1;
			unsigned long DM : 2;
			unsigned long SARA : 5;
			unsigned long  : 1;
			unsigned long SM : 2;
			unsigned long DIR : 1;
			unsigned long AMS : 1;
			unsigned long  : 14;
#else
			unsigned long  : 14;
			unsigned long AMS : 1;
			unsigned long DIR : 1;
			unsigned long SM : 2;
			unsigned long  : 1;
			unsigned long SARA : 5;
			unsigned long DM : 2;
			unsigned long  : 1;
			unsigned long DARA : 5;
#endif
	} BIT;
	} EDMAMD;
	char           wk1[4];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DTE : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char DTE : 1;
#endif
	} BIT;
	} EDMCNT;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SWREQ : 1;
			unsigned char  : 3;
			unsigned char CLRS : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char CLRS : 1;
			unsigned char  : 3;
			unsigned char SWREQ : 1;
#endif
	} BIT;
	} EDMREQ;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ESIF : 1;
			unsigned char  : 3;
			unsigned char DTIF : 1;
			unsigned char  : 2;
			unsigned char ACT : 1;
#else
			unsigned char ACT : 1;
			unsigned char  : 2;
			unsigned char DTIF : 1;
			unsigned char  : 3;
			unsigned char ESIF : 1;
#endif
	} BIT;
	} EDMSTS;
	char           wk2[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DREQS : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char DREQS : 2;
#endif
	} BIT;
	} EDMRMD;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char EREQ : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char EREQ : 1;
#endif
	} BIT;
	} EDMERF;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PREQ : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char PREQ : 1;
#endif
	} BIT;
	} EDMPRF;
} st_exdmac1_t;

typedef struct st_flash {
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ROMCEN : 1;
			unsigned short  : 15;
#else
			unsigned short  : 15;
			unsigned short ROMCEN : 1;
#endif
	} BIT;
	} ROMCE;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ROMCIV : 1;
			unsigned short  : 15;
#else
			unsigned short  : 15;
			unsigned short ROMCIV : 1;
#endif
	} BIT;
	} ROMCIV;
	char           wk1[58];
	unsigned long  NCRG0;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 1;
			unsigned long NC1E : 1;
			unsigned long NC2E : 1;
			unsigned long NC3E : 1;
			unsigned long NCSZ : 17;
			unsigned long  : 11;
#else
			unsigned long  : 11;
			unsigned long NCSZ : 17;
			unsigned long NC3E : 1;
			unsigned long NC2E : 1;
			unsigned long NC1E : 1;
			unsigned long  : 1;
#endif
	} BIT;
	} NCRC0;
	unsigned long  NCRG1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 1;
			unsigned long NC1E : 1;
			unsigned long NC2E : 1;
			unsigned long NC3E : 1;
			unsigned long NCSZ : 17;
			unsigned long  : 11;
#else
			unsigned long  : 11;
			unsigned long NCSZ : 17;
			unsigned long NC3E : 1;
			unsigned long NC2E : 1;
			unsigned long NC1E : 1;
			unsigned long  : 1;
#endif
	} BIT;
	} NCRC1;
	char           wk2[45638];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char FLWE : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char FLWE : 2;
#endif
	} BIT;
	} FWEPROR;
	char           wk3[7798185];
	unsigned char  EEPFCLK;
	char           wk4[8143];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 3;
			unsigned char DFAE : 1;
			unsigned char CMDLK : 1;
			unsigned char  : 2;
			unsigned char CFAE : 1;
#else
			unsigned char CFAE : 1;
			unsigned char  : 2;
			unsigned char CMDLK : 1;
			unsigned char DFAE : 1;
			unsigned char  : 3;
#endif
	} BIT;
	} FASTAT;
	char           wk5[3];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 3;
			unsigned char DFAEIE : 1;
			unsigned char CMDLKIE : 1;
			unsigned char  : 2;
			unsigned char CFAEIE : 1;
#else
			unsigned char CFAEIE : 1;
			unsigned char  : 2;
			unsigned char CMDLKIE : 1;
			unsigned char DFAEIE : 1;
			unsigned char  : 3;
#endif
	} BIT;
	} FAEINT;
	char           wk6[3];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char FRDYIE : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char FRDYIE : 1;
#endif
	} BIT;
	} FRDYIE;
	char           wk7[23];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long FSADDR : 32;
#else
			unsigned long FSADDR : 32;
#endif
	} BIT;
	} FSADDR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long FEADDR : 32;
#else
			unsigned long FEADDR : 32;
#endif
	} BIT;
	} FEADDR;
	char           wk8[72];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 6;
			unsigned long FLWEERR : 1;
			unsigned long  : 1;
			unsigned long PRGSPD : 1;
			unsigned long ERSSPD : 1;
			unsigned long DBFULL : 1;
			unsigned long SUSRDY : 1;
			unsigned long PRGERR : 1;
			unsigned long ERSERR : 1;
			unsigned long ILGLERR : 1;
			unsigned long FRDY : 1;
			unsigned long  : 4;
			unsigned long OTERR : 1;
			unsigned long SECERR : 1;
			unsigned long FESETERR : 1;
			unsigned long ILGCOMERR : 1;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long ILGCOMERR : 1;
			unsigned long FESETERR : 1;
			unsigned long SECERR : 1;
			unsigned long OTERR : 1;
			unsigned long  : 4;
			unsigned long FRDY : 1;
			unsigned long ILGLERR : 1;
			unsigned long ERSERR : 1;
			unsigned long PRGERR : 1;
			unsigned long SUSRDY : 1;
			unsigned long DBFULL : 1;
			unsigned long ERSSPD : 1;
			unsigned long PRGSPD : 1;
			unsigned long  : 1;
			unsigned long FLWEERR : 1;
			unsigned long  : 6;
#endif
	} BIT;
	} FSTATR;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short FENTRYC : 1;
			unsigned short  : 6;
			unsigned short FENTRYD : 1;
			unsigned short KEY : 8;
#else
			unsigned short KEY : 8;
			unsigned short FENTRYD : 1;
			unsigned short  : 6;
			unsigned short FENTRYC : 1;
#endif
	} BIT;
	} FENTRYR;
	char           wk9[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short SUINIT : 1;
			unsigned short  : 7;
			unsigned short KEY : 8;
#else
			unsigned short KEY : 8;
			unsigned short  : 7;
			unsigned short SUINIT : 1;
#endif
	} BIT;
	} FSUINITR;
	char           wk10[18];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PCMDR : 8;
			unsigned short CMDR : 8;
#else
			unsigned short CMDR : 8;
			unsigned short PCMDR : 8;
#endif
	} BIT;
	} FCMDR;
	char           wk11[46];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCDIR : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char BCDIR : 1;
#endif
	} BIT;
	} FBCCNT;
	char           wk12[3];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCST : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char BCST : 1;
#endif
	} BIT;
	} FBCSTAT;
	char           wk13[3];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PSADR : 17;
			unsigned long  : 15;
#else
			unsigned long  : 15;
			unsigned long PSADR : 17;
#endif
	} BIT;
	} FPSADDR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long FAWS : 12;
			unsigned long  : 3;
			unsigned long FSPR : 1;
			unsigned long FAWE : 12;
			unsigned long  : 3;
			unsigned long BTFLG : 1;
#else
			unsigned long BTFLG : 1;
			unsigned long  : 3;
			unsigned long FAWE : 12;
			unsigned long FSPR : 1;
			unsigned long  : 3;
			unsigned long FAWS : 12;
#endif
	} BIT;
	} FAWMON;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ESUSPMD : 1;
			unsigned short  : 15;
#else
			unsigned short  : 15;
			unsigned short ESUSPMD : 1;
#endif
	} BIT;
	} FCPSR;
	char           wk14[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PCKA : 8;
			unsigned short KEY : 8;
#else
			unsigned short KEY : 8;
			unsigned short PCKA : 8;
#endif
	} BIT;
	} FPCKAR;
	char           wk15[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short SAS : 2;
			unsigned short  : 6;
			unsigned short KEY : 8;
#else
			unsigned short KEY : 8;
			unsigned short  : 6;
			unsigned short SAS : 2;
#endif
	} BIT;
	} FSUACR;
} st_flash_t;

typedef struct st_glcdc {
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long B : 8;
			unsigned long G : 8;
			unsigned long R : 8;
			unsigned long A : 8;
#else
			unsigned long A : 8;
			unsigned long R : 8;
			unsigned long G : 8;
			unsigned long B : 8;
#endif
	} BIT;
	} GR1CLUT0[256];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long B : 8;
			unsigned long G : 8;
			unsigned long R : 8;
			unsigned long A : 8;
#else
			unsigned long A : 8;
			unsigned long R : 8;
			unsigned long G : 8;
			unsigned long B : 8;
#endif
	} BIT;
	} GR1CLUT1[256];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long B : 8;
			unsigned long G : 8;
			unsigned long R : 8;
			unsigned long A : 8;
#else
			unsigned long A : 8;
			unsigned long R : 8;
			unsigned long G : 8;
			unsigned long B : 8;
#endif
	} BIT;
	} GR2CLUT0[256];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long B : 8;
			unsigned long G : 8;
			unsigned long R : 8;
			unsigned long A : 8;
#else
			unsigned long A : 8;
			unsigned long R : 8;
			unsigned long G : 8;
			unsigned long B : 8;
#endif
	} BIT;
	} GR2CLUT1[256];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EN : 1;
			unsigned long  : 7;
			unsigned long VEN : 1;
			unsigned long  : 7;
			unsigned long SWRST : 1;
			unsigned long  : 15;
#else
			unsigned long  : 15;
			unsigned long SWRST : 1;
			unsigned long  : 7;
			unsigned long VEN : 1;
			unsigned long  : 7;
			unsigned long EN : 1;
#endif
	} BIT;
	} BGEN;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long FH : 11;
			unsigned long  : 5;
			unsigned long FV : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long FV : 11;
			unsigned long  : 5;
			unsigned long FH : 11;
#endif
	} BIT;
	} BGPERI;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long HP : 4;
			unsigned long  : 12;
			unsigned long VP : 4;
			unsigned long  : 12;
#else
			unsigned long  : 12;
			unsigned long VP : 4;
			unsigned long  : 12;
			unsigned long HP : 4;
#endif
	} BIT;
	} BGSYNC;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long VW : 11;
			unsigned long  : 5;
			unsigned long VP : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long VP : 11;
			unsigned long  : 5;
			unsigned long VW : 11;
#endif
	} BIT;
	} BGVSIZE;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long HW : 11;
			unsigned long  : 5;
			unsigned long HP : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long HP : 11;
			unsigned long  : 5;
			unsigned long HW : 11;
#endif
	} BIT;
	} BGHSIZE;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long B : 8;
			unsigned long G : 8;
			unsigned long R : 8;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long R : 8;
			unsigned long G : 8;
			unsigned long B : 8;
#endif
	} BIT;
	} BGCOLOR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EN : 1;
			unsigned long  : 7;
			unsigned long VEN : 1;
			unsigned long  : 7;
			unsigned long SWRST : 1;
			unsigned long  : 15;
#else
			unsigned long  : 15;
			unsigned long SWRST : 1;
			unsigned long  : 7;
			unsigned long VEN : 1;
			unsigned long  : 7;
			unsigned long EN : 1;
#endif
	} BIT;
	} BGMON;
	char           wk0[228];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long VEN : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long VEN : 1;
#endif
	} BIT;
	} GR1VEN;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RENB : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long RENB : 1;
#endif
	} BIT;
	} GR1FLMRD;
	char           wk1[4];
	unsigned long  GR1FLM2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 16;
			unsigned long LNOFF : 16;
#else
			unsigned long LNOFF : 16;
			unsigned long  : 16;
#endif
	} BIT;
	} GR1FLM3;
	char           wk2[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long DATANUM : 16;
			unsigned long LNNUM : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long LNNUM : 11;
			unsigned long DATANUM : 16;
#endif
	} BIT;
	} GR1FLM5;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 28;
			unsigned long FORMAT : 3;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long FORMAT : 3;
			unsigned long  : 28;
#endif
	} BIT;
	} GR1FLM6;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long DISPSEL : 2;
			unsigned long  : 2;
			unsigned long GRCDISPON : 1;
			unsigned long  : 3;
			unsigned long ARCDISPON : 1;
			unsigned long  : 3;
			unsigned long ARCON : 1;
			unsigned long  : 19;
#else
			unsigned long  : 19;
			unsigned long ARCON : 1;
			unsigned long  : 3;
			unsigned long ARCDISPON : 1;
			unsigned long  : 3;
			unsigned long GRCDISPON : 1;
			unsigned long  : 2;
			unsigned long DISPSEL : 2;
#endif
	} BIT;
	} GR1AB1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GRCVW : 11;
			unsigned long  : 5;
			unsigned long GRCVS : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GRCVS : 11;
			unsigned long  : 5;
			unsigned long GRCVW : 11;
#endif
	} BIT;
	} GR1AB2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GRCHW : 11;
			unsigned long  : 5;
			unsigned long GRCHS : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GRCHS : 11;
			unsigned long  : 5;
			unsigned long GRCHW : 11;
#endif
	} BIT;
	} GR1AB3;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ARCVW : 11;
			unsigned long  : 5;
			unsigned long ARCVS : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long ARCVS : 11;
			unsigned long  : 5;
			unsigned long ARCVW : 11;
#endif
	} BIT;
	} GR1AB4;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ARCHW : 11;
			unsigned long  : 5;
			unsigned long ARCHS : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long ARCHS : 11;
			unsigned long  : 5;
			unsigned long ARCHW : 11;
#endif
	} BIT;
	} GR1AB5;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ARCRATE : 8;
			unsigned long  : 8;
			unsigned long ARCCOEF : 9;
			unsigned long  : 7;
#else
			unsigned long  : 7;
			unsigned long ARCCOEF : 9;
			unsigned long  : 8;
			unsigned long ARCRATE : 8;
#endif
	} BIT;
	} GR1AB6;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CKON : 1;
			unsigned long  : 15;
			unsigned long ARCDEF : 8;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long ARCDEF : 8;
			unsigned long  : 15;
			unsigned long CKON : 1;
#endif
	} BIT;
	} GR1AB7;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CKKR : 8;
			unsigned long CKKB : 8;
			unsigned long CKKG : 8;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long CKKG : 8;
			unsigned long CKKB : 8;
			unsigned long CKKR : 8;
#endif
	} BIT;
	} GR1AB8;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CKR : 8;
			unsigned long CKB : 8;
			unsigned long CKG : 8;
			unsigned long CKA : 8;
#else
			unsigned long CKA : 8;
			unsigned long CKG : 8;
			unsigned long CKB : 8;
			unsigned long CKR : 8;
#endif
	} BIT;
	} GR1AB9;
	char           wk3[8];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long R : 8;
			unsigned long B : 8;
			unsigned long G : 8;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long G : 8;
			unsigned long B : 8;
			unsigned long R : 8;
#endif
	} BIT;
	} GR1BASE;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long LINE : 11;
			unsigned long  : 5;
			unsigned long SEL : 1;
			unsigned long  : 15;
#else
			unsigned long  : 15;
			unsigned long SEL : 1;
			unsigned long  : 5;
			unsigned long LINE : 11;
#endif
	} BIT;
	} GR1CLUTINT;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ARCST : 1;
			unsigned long  : 15;
			unsigned long UFST : 1;
			unsigned long  : 15;
#else
			unsigned long  : 15;
			unsigned long UFST : 1;
			unsigned long  : 15;
			unsigned long ARCST : 1;
#endif
	} BIT;
	} GR1MON;
	char           wk4[168];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long VEN : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long VEN : 1;
#endif
	} BIT;
	} GR2VEN;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RENB : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long RENB : 1;
#endif
	} BIT;
	} GR2FLMRD;
	char           wk5[4];
	unsigned long  GR2FLM2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 16;
			unsigned long LNOFF : 16;
#else
			unsigned long LNOFF : 16;
			unsigned long  : 16;
#endif
	} BIT;
	} GR2FLM3;
	char           wk6[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long DATANUM : 16;
			unsigned long LNNUM : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long LNNUM : 11;
			unsigned long DATANUM : 16;
#endif
	} BIT;
	} GR2FLM5;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 28;
			unsigned long FORMAT : 3;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long FORMAT : 3;
			unsigned long  : 28;
#endif
	} BIT;
	} GR2FLM6;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long DISPSEL : 2;
			unsigned long  : 2;
			unsigned long GRCDISPON : 1;
			unsigned long  : 3;
			unsigned long ARCDISPON : 1;
			unsigned long  : 3;
			unsigned long ARCON : 1;
			unsigned long  : 19;
#else
			unsigned long  : 19;
			unsigned long ARCON : 1;
			unsigned long  : 3;
			unsigned long ARCDISPON : 1;
			unsigned long  : 3;
			unsigned long GRCDISPON : 1;
			unsigned long  : 2;
			unsigned long DISPSEL : 2;
#endif
	} BIT;
	} GR2AB1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GRCVW : 11;
			unsigned long  : 5;
			unsigned long GRCVS : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GRCVS : 11;
			unsigned long  : 5;
			unsigned long GRCVW : 11;
#endif
	} BIT;
	} GR2AB2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GRCHW : 11;
			unsigned long  : 5;
			unsigned long GRCHS : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GRCHS : 11;
			unsigned long  : 5;
			unsigned long GRCHW : 11;
#endif
	} BIT;
	} GR2AB3;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ARCVW : 11;
			unsigned long  : 5;
			unsigned long ARCVS : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long ARCVS : 11;
			unsigned long  : 5;
			unsigned long ARCVW : 11;
#endif
	} BIT;
	} GR2AB4;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ARCHW : 11;
			unsigned long  : 5;
			unsigned long ARCHS : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long ARCHS : 11;
			unsigned long  : 5;
			unsigned long ARCHW : 11;
#endif
	} BIT;
	} GR2AB5;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ARCRATE : 8;
			unsigned long  : 8;
			unsigned long ARCCOEF : 9;
			unsigned long  : 7;
#else
			unsigned long  : 7;
			unsigned long ARCCOEF : 9;
			unsigned long  : 8;
			unsigned long ARCRATE : 8;
#endif
	} BIT;
	} GR2AB6;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CKON : 1;
			unsigned long  : 15;
			unsigned long ARCDEF : 8;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long ARCDEF : 8;
			unsigned long  : 15;
			unsigned long CKON : 1;
#endif
	} BIT;
	} GR2AB7;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CKKR : 8;
			unsigned long CKKB : 8;
			unsigned long CKKG : 8;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long CKKG : 8;
			unsigned long CKKB : 8;
			unsigned long CKKR : 8;
#endif
	} BIT;
	} GR2AB8;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CKR : 8;
			unsigned long CKB : 8;
			unsigned long CKG : 8;
			unsigned long CKA : 8;
#else
			unsigned long CKA : 8;
			unsigned long CKG : 8;
			unsigned long CKB : 8;
			unsigned long CKR : 8;
#endif
	} BIT;
	} GR2AB9;
	char           wk7[8];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long R : 8;
			unsigned long B : 8;
			unsigned long G : 8;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long G : 8;
			unsigned long B : 8;
			unsigned long R : 8;
#endif
	} BIT;
	} GR2BASE;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long LINE : 11;
			unsigned long  : 5;
			unsigned long SEL : 1;
			unsigned long  : 15;
#else
			unsigned long  : 15;
			unsigned long SEL : 1;
			unsigned long  : 5;
			unsigned long LINE : 11;
#endif
	} BIT;
	} GR2CLUTINT;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ARCST : 1;
			unsigned long  : 15;
			unsigned long UFST : 1;
			unsigned long  : 15;
#else
			unsigned long  : 15;
			unsigned long UFST : 1;
			unsigned long  : 15;
			unsigned long ARCST : 1;
#endif
	} BIT;
	} GR2MON;
	char           wk8[168];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long VEN : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long VEN : 1;
#endif
	} BIT;
	} GAMGVEN;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAMON : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long GAMON : 1;
#endif
	} BIT;
	} GAMSW;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN01 : 11;
			unsigned long  : 5;
			unsigned long GAIN00 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN00 : 11;
			unsigned long  : 5;
			unsigned long GAIN01 : 11;
#endif
	} BIT;
	} GAMGLUT1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN03 : 11;
			unsigned long  : 5;
			unsigned long GAIN02 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN02 : 11;
			unsigned long  : 5;
			unsigned long GAIN03 : 11;
#endif
	} BIT;
	} GAMGLUT2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN05 : 11;
			unsigned long  : 5;
			unsigned long GAIN04 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN04 : 11;
			unsigned long  : 5;
			unsigned long GAIN05 : 11;
#endif
	} BIT;
	} GAMGLUT3;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN07 : 11;
			unsigned long  : 5;
			unsigned long GAIN06 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN06 : 11;
			unsigned long  : 5;
			unsigned long GAIN07 : 11;
#endif
	} BIT;
	} GAMGLUT4;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN09 : 11;
			unsigned long  : 5;
			unsigned long GAIN08 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN08 : 11;
			unsigned long  : 5;
			unsigned long GAIN09 : 11;
#endif
	} BIT;
	} GAMGLUT5;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN11 : 11;
			unsigned long  : 5;
			unsigned long GAIN10 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN10 : 11;
			unsigned long  : 5;
			unsigned long GAIN11 : 11;
#endif
	} BIT;
	} GAMGLUT6;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN13 : 11;
			unsigned long  : 5;
			unsigned long GAIN12 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN12 : 11;
			unsigned long  : 5;
			unsigned long GAIN13 : 11;
#endif
	} BIT;
	} GAMGLUT7;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN15 : 11;
			unsigned long  : 5;
			unsigned long GAIN14 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN14 : 11;
			unsigned long  : 5;
			unsigned long GAIN15 : 11;
#endif
	} BIT;
	} GAMGLUT8;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TH03 : 10;
			unsigned long TH02 : 10;
			unsigned long TH01 : 10;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long TH01 : 10;
			unsigned long TH02 : 10;
			unsigned long TH03 : 10;
#endif
	} BIT;
	} GAMGAREA1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TH06 : 10;
			unsigned long TH05 : 10;
			unsigned long TH04 : 10;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long TH04 : 10;
			unsigned long TH05 : 10;
			unsigned long TH06 : 10;
#endif
	} BIT;
	} GAMGAREA2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TH09 : 10;
			unsigned long TH08 : 10;
			unsigned long TH07 : 10;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long TH07 : 10;
			unsigned long TH08 : 10;
			unsigned long TH09 : 10;
#endif
	} BIT;
	} GAMGAREA3;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TH12 : 10;
			unsigned long TH11 : 10;
			unsigned long TH10 : 10;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long TH10 : 10;
			unsigned long TH11 : 10;
			unsigned long TH12 : 10;
#endif
	} BIT;
	} GAMGAREA4;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TH15 : 10;
			unsigned long TH14 : 10;
			unsigned long TH13 : 10;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long TH13 : 10;
			unsigned long TH14 : 10;
			unsigned long TH15 : 10;
#endif
	} BIT;
	} GAMGAREA5;
	char           wk9[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long VEN : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long VEN : 1;
#endif
	} BIT;
	} GAMBVEN;
	char           wk10[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN01 : 11;
			unsigned long  : 5;
			unsigned long GAIN00 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN00 : 11;
			unsigned long  : 5;
			unsigned long GAIN01 : 11;
#endif
	} BIT;
	} GAMBLUT1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN03 : 11;
			unsigned long  : 5;
			unsigned long GAIN02 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN02 : 11;
			unsigned long  : 5;
			unsigned long GAIN03 : 11;
#endif
	} BIT;
	} GAMBLUT2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN05 : 11;
			unsigned long  : 5;
			unsigned long GAIN04 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN04 : 11;
			unsigned long  : 5;
			unsigned long GAIN05 : 11;
#endif
	} BIT;
	} GAMBLUT3;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN07 : 11;
			unsigned long  : 5;
			unsigned long GAIN06 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN06 : 11;
			unsigned long  : 5;
			unsigned long GAIN07 : 11;
#endif
	} BIT;
	} GAMBLUT4;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN09 : 11;
			unsigned long  : 5;
			unsigned long GAIN08 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN08 : 11;
			unsigned long  : 5;
			unsigned long GAIN09 : 11;
#endif
	} BIT;
	} GAMBLUT5;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN11 : 11;
			unsigned long  : 5;
			unsigned long GAIN10 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN10 : 11;
			unsigned long  : 5;
			unsigned long GAIN11 : 11;
#endif
	} BIT;
	} GAMBLUT6;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN13 : 11;
			unsigned long  : 5;
			unsigned long GAIN12 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN12 : 11;
			unsigned long  : 5;
			unsigned long GAIN13 : 11;
#endif
	} BIT;
	} GAMBLUT7;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN15 : 11;
			unsigned long  : 5;
			unsigned long GAIN14 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN14 : 11;
			unsigned long  : 5;
			unsigned long GAIN15 : 11;
#endif
	} BIT;
	} GAMBLUT8;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TH03 : 10;
			unsigned long TH02 : 10;
			unsigned long TH01 : 10;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long TH01 : 10;
			unsigned long TH02 : 10;
			unsigned long TH03 : 10;
#endif
	} BIT;
	} GAMBAREA1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TH06 : 10;
			unsigned long TH05 : 10;
			unsigned long TH04 : 10;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long TH04 : 10;
			unsigned long TH05 : 10;
			unsigned long TH06 : 10;
#endif
	} BIT;
	} GAMBAREA2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TH09 : 10;
			unsigned long TH08 : 10;
			unsigned long TH07 : 10;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long TH07 : 10;
			unsigned long TH08 : 10;
			unsigned long TH09 : 10;
#endif
	} BIT;
	} GAMBAREA3;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TH12 : 10;
			unsigned long TH11 : 10;
			unsigned long TH10 : 10;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long TH10 : 10;
			unsigned long TH11 : 10;
			unsigned long TH12 : 10;
#endif
	} BIT;
	} GAMBAREA4;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TH15 : 10;
			unsigned long TH14 : 10;
			unsigned long TH13 : 10;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long TH13 : 10;
			unsigned long TH14 : 10;
			unsigned long TH15 : 10;
#endif
	} BIT;
	} GAMBAREA5;
	char           wk11[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long VEN : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long VEN : 1;
#endif
	} BIT;
	} GAMRVEN;
	char           wk12[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN01 : 11;
			unsigned long  : 5;
			unsigned long GAIN00 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN00 : 11;
			unsigned long  : 5;
			unsigned long GAIN01 : 11;
#endif
	} BIT;
	} GAMRLUT1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN03 : 11;
			unsigned long  : 5;
			unsigned long GAIN02 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN02 : 11;
			unsigned long  : 5;
			unsigned long GAIN03 : 11;
#endif
	} BIT;
	} GAMRLUT2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN05 : 11;
			unsigned long  : 5;
			unsigned long GAIN04 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN04 : 11;
			unsigned long  : 5;
			unsigned long GAIN05 : 11;
#endif
	} BIT;
	} GAMRLUT3;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN07 : 11;
			unsigned long  : 5;
			unsigned long GAIN06 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN06 : 11;
			unsigned long  : 5;
			unsigned long GAIN07 : 11;
#endif
	} BIT;
	} GAMRLUT4;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN09 : 11;
			unsigned long  : 5;
			unsigned long GAIN08 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN08 : 11;
			unsigned long  : 5;
			unsigned long GAIN09 : 11;
#endif
	} BIT;
	} GAMRLUT5;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN11 : 11;
			unsigned long  : 5;
			unsigned long GAIN10 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN10 : 11;
			unsigned long  : 5;
			unsigned long GAIN11 : 11;
#endif
	} BIT;
	} GAMRLUT6;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN13 : 11;
			unsigned long  : 5;
			unsigned long GAIN12 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN12 : 11;
			unsigned long  : 5;
			unsigned long GAIN13 : 11;
#endif
	} BIT;
	} GAMRLUT7;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GAIN15 : 11;
			unsigned long  : 5;
			unsigned long GAIN14 : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long GAIN14 : 11;
			unsigned long  : 5;
			unsigned long GAIN15 : 11;
#endif
	} BIT;
	} GAMRLUT8;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TH03 : 10;
			unsigned long TH02 : 10;
			unsigned long TH01 : 10;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long TH01 : 10;
			unsigned long TH02 : 10;
			unsigned long TH03 : 10;
#endif
	} BIT;
	} GAMRAREA1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TH06 : 10;
			unsigned long TH05 : 10;
			unsigned long TH04 : 10;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long TH04 : 10;
			unsigned long TH05 : 10;
			unsigned long TH06 : 10;
#endif
	} BIT;
	} GAMRAREA2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TH09 : 10;
			unsigned long TH08 : 10;
			unsigned long TH07 : 10;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long TH07 : 10;
			unsigned long TH08 : 10;
			unsigned long TH09 : 10;
#endif
	} BIT;
	} GAMRAREA3;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TH12 : 10;
			unsigned long TH11 : 10;
			unsigned long TH10 : 10;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long TH10 : 10;
			unsigned long TH11 : 10;
			unsigned long TH12 : 10;
#endif
	} BIT;
	} GAMRAREA4;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TH15 : 10;
			unsigned long TH14 : 10;
			unsigned long TH13 : 10;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long TH13 : 10;
			unsigned long TH14 : 10;
			unsigned long TH15 : 10;
#endif
	} BIT;
	} GAMRAREA5;
	char           wk13[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long VEN : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long VEN : 1;
#endif
	} BIT;
	} OUTVEN;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PHASE : 2;
			unsigned long  : 2;
			unsigned long DIRSEL : 1;
			unsigned long  : 4;
			unsigned long FRQSEL : 1;
			unsigned long  : 2;
			unsigned long FORMAT : 2;
			unsigned long  : 10;
			unsigned long SWAPON : 1;
			unsigned long  : 3;
			unsigned long ENDIANON : 1;
			unsigned long  : 3;
#else
			unsigned long  : 3;
			unsigned long ENDIANON : 1;
			unsigned long  : 3;
			unsigned long SWAPON : 1;
			unsigned long  : 10;
			unsigned long FORMAT : 2;
			unsigned long  : 2;
			unsigned long FRQSEL : 1;
			unsigned long  : 4;
			unsigned long DIRSEL : 1;
			unsigned long  : 2;
			unsigned long PHASE : 2;
#endif
	} BIT;
	} OUTSET;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long BRTG : 10;
			unsigned long  : 22;
#else
			unsigned long  : 22;
			unsigned long BRTG : 10;
#endif
	} BIT;
	} BRIGHT1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long BRTR : 10;
			unsigned long  : 6;
			unsigned long BRTB : 10;
			unsigned long  : 6;
#else
			unsigned long  : 6;
			unsigned long BRTB : 10;
			unsigned long  : 6;
			unsigned long BRTR : 10;
#endif
	} BIT;
	} BRIGHT2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CONTR : 8;
			unsigned long CONTB : 8;
			unsigned long CONTG : 8;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long CONTG : 8;
			unsigned long CONTB : 8;
			unsigned long CONTR : 8;
#endif
	} BIT;
	} CONTRAST;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PD : 2;
			unsigned long  : 2;
			unsigned long PC : 2;
			unsigned long  : 2;
			unsigned long PB : 2;
			unsigned long  : 2;
			unsigned long PA : 2;
			unsigned long  : 2;
			unsigned long FORM : 2;
			unsigned long  : 2;
			unsigned long SEL : 2;
			unsigned long  : 10;
#else
			unsigned long  : 10;
			unsigned long SEL : 2;
			unsigned long  : 2;
			unsigned long FORM : 2;
			unsigned long  : 2;
			unsigned long PA : 2;
			unsigned long  : 2;
			unsigned long PB : 2;
			unsigned long  : 2;
			unsigned long PC : 2;
			unsigned long  : 2;
			unsigned long PD : 2;
#endif
	} BIT;
	} PANELDTHA;
	char           wk14[12];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 3;
			unsigned long TCON3EDG : 1;
			unsigned long TCON2EDG : 1;
			unsigned long TCON1EDG : 1;
			unsigned long TCON0EDG : 1;
			unsigned long  : 1;
			unsigned long LCDEDG : 1;
			unsigned long  : 3;
			unsigned long FRONTGAM : 1;
			unsigned long  : 19;
#else
			unsigned long  : 19;
			unsigned long FRONTGAM : 1;
			unsigned long  : 3;
			unsigned long LCDEDG : 1;
			unsigned long  : 1;
			unsigned long TCON0EDG : 1;
			unsigned long TCON1EDG : 1;
			unsigned long TCON2EDG : 1;
			unsigned long TCON3EDG : 1;
			unsigned long  : 3;
#endif
	} BIT;
	} CLKPHASE;
	char           wk15[28];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long OFFSET : 11;
			unsigned long  : 5;
			unsigned long HALF : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long HALF : 11;
			unsigned long  : 5;
			unsigned long OFFSET : 11;
#endif
	} BIT;
	} TCONTIM;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long VW : 11;
			unsigned long  : 5;
			unsigned long VS : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long VS : 11;
			unsigned long  : 5;
			unsigned long VW : 11;
#endif
	} BIT;
	} TCONSTVA1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long SEL : 3;
			unsigned long  : 1;
			unsigned long INV : 1;
			unsigned long  : 27;
#else
			unsigned long  : 27;
			unsigned long INV : 1;
			unsigned long  : 1;
			unsigned long SEL : 3;
#endif
	} BIT;
	} TCONSTVA2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long VW : 11;
			unsigned long  : 5;
			unsigned long VS : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long VS : 11;
			unsigned long  : 5;
			unsigned long VW : 11;
#endif
	} BIT;
	} TCONSTVB1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long SEL : 3;
			unsigned long  : 1;
			unsigned long INV : 1;
			unsigned long  : 27;
#else
			unsigned long  : 27;
			unsigned long INV : 1;
			unsigned long  : 1;
			unsigned long SEL : 3;
#endif
	} BIT;
	} TCONSTVB2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long HW : 11;
			unsigned long  : 5;
			unsigned long HS : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long HS : 11;
			unsigned long  : 5;
			unsigned long HW : 11;
#endif
	} BIT;
	} TCONSTHA1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long SEL : 3;
			unsigned long  : 1;
			unsigned long INV : 1;
			unsigned long  : 3;
			unsigned long HSSEL : 1;
			unsigned long  : 23;
#else
			unsigned long  : 23;
			unsigned long HSSEL : 1;
			unsigned long  : 3;
			unsigned long INV : 1;
			unsigned long  : 1;
			unsigned long SEL : 3;
#endif
	} BIT;
	} TCONSTHA2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long HW : 11;
			unsigned long  : 5;
			unsigned long HS : 11;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long HS : 11;
			unsigned long  : 5;
			unsigned long HW : 11;
#endif
	} BIT;
	} TCONSTHB1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long SEL : 3;
			unsigned long  : 1;
			unsigned long INV : 1;
			unsigned long  : 3;
			unsigned long HSSEL : 1;
			unsigned long  : 23;
#else
			unsigned long  : 23;
			unsigned long HSSEL : 1;
			unsigned long  : 3;
			unsigned long INV : 1;
			unsigned long  : 1;
			unsigned long SEL : 3;
#endif
	} BIT;
	} TCONSTHB2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long INV : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long INV : 1;
#endif
	} BIT;
	} TCONDE;
	char           wk16[20];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long VPOSDTC : 1;
			unsigned long GR1UFDTC : 1;
			unsigned long GR2UFDTC : 1;
			unsigned long  : 29;
#else
			unsigned long  : 29;
			unsigned long GR2UFDTC : 1;
			unsigned long GR1UFDTC : 1;
			unsigned long VPOSDTC : 1;
#endif
	} BIT;
	} DTCTEN;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long VPOSINTEN : 1;
			unsigned long GR1UFINTEN : 1;
			unsigned long GR2UFINTEN : 1;
			unsigned long  : 29;
#else
			unsigned long  : 29;
			unsigned long GR2UFINTEN : 1;
			unsigned long GR1UFINTEN : 1;
			unsigned long VPOSINTEN : 1;
#endif
	} BIT;
	} INTEN;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long VPOSCLR : 1;
			unsigned long GR1UFCLR : 1;
			unsigned long GR2UFCLR : 1;
			unsigned long  : 29;
#else
			unsigned long  : 29;
			unsigned long GR2UFCLR : 1;
			unsigned long GR1UFCLR : 1;
			unsigned long VPOSCLR : 1;
#endif
	} BIT;
	} STCLR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long VPOS : 1;
			unsigned long GR1UF : 1;
			unsigned long GR2UF : 1;
			unsigned long  : 29;
#else
			unsigned long  : 29;
			unsigned long GR2UF : 1;
			unsigned long GR1UF : 1;
			unsigned long VPOS : 1;
#endif
	} BIT;
	} STMON;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long DCDR : 6;
			unsigned long CLKEN : 1;
			unsigned long  : 1;
			unsigned long CLKSEL : 1;
			unsigned long  : 3;
			unsigned long PIXSEL : 1;
			unsigned long  : 19;
#else
			unsigned long  : 19;
			unsigned long PIXSEL : 1;
			unsigned long  : 3;
			unsigned long CLKSEL : 1;
			unsigned long  : 1;
			unsigned long CLKEN : 1;
			unsigned long DCDR : 6;
#endif
	} BIT;
	} PANELCLK;
} st_glcdc_t;

typedef struct st_gptw {
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long WP : 1;
			unsigned long STRWP : 1;
			unsigned long STPWP : 1;
			unsigned long CLRWP : 1;
			unsigned long CMNWP : 1;
			unsigned long  : 3;
			unsigned long PRKEY : 8;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long PRKEY : 8;
			unsigned long  : 3;
			unsigned long CMNWP : 1;
			unsigned long CLRWP : 1;
			unsigned long STPWP : 1;
			unsigned long STRWP : 1;
			unsigned long WP : 1;
#endif
	} BIT;
	} GTWP;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CSTRT0 : 1;
			unsigned long CSTRT1 : 1;
			unsigned long CSTRT2 : 1;
			unsigned long CSTRT3 : 1;
			unsigned long  : 28;
#else
			unsigned long  : 28;
			unsigned long CSTRT3 : 1;
			unsigned long CSTRT2 : 1;
			unsigned long CSTRT1 : 1;
			unsigned long CSTRT0 : 1;
#endif
	} BIT;
	} GTSTR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CSTOP0 : 1;
			unsigned long CSTOP1 : 1;
			unsigned long CSTOP2 : 1;
			unsigned long CSTOP3 : 1;
			unsigned long  : 28;
#else
			unsigned long  : 28;
			unsigned long CSTOP3 : 1;
			unsigned long CSTOP2 : 1;
			unsigned long CSTOP1 : 1;
			unsigned long CSTOP0 : 1;
#endif
	} BIT;
	} GTSTP;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CCLR0 : 1;
			unsigned long CCLR1 : 1;
			unsigned long CCLR2 : 1;
			unsigned long CCLR3 : 1;
			unsigned long  : 28;
#else
			unsigned long  : 28;
			unsigned long CCLR3 : 1;
			unsigned long CCLR2 : 1;
			unsigned long CCLR1 : 1;
			unsigned long CCLR0 : 1;
#endif
	} BIT;
	} GTCLR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long SSGTRGAR : 1;
			unsigned long SSGTRGAF : 1;
			unsigned long SSGTRGBR : 1;
			unsigned long SSGTRGBF : 1;
			unsigned long SSGTRGCR : 1;
			unsigned long SSGTRGCF : 1;
			unsigned long SSGTRGDR : 1;
			unsigned long SSGTRGDF : 1;
			unsigned long SSCARBL : 1;
			unsigned long SSCARBH : 1;
			unsigned long SSCAFBL : 1;
			unsigned long SSCAFBH : 1;
			unsigned long SSCBRAL : 1;
			unsigned long SSCBRAH : 1;
			unsigned long SSCBFAL : 1;
			unsigned long SSCBFAH : 1;
			unsigned long SSELCA : 1;
			unsigned long SSELCB : 1;
			unsigned long SSELCC : 1;
			unsigned long SSELCD : 1;
			unsigned long SSELCE : 1;
			unsigned long SSELCF : 1;
			unsigned long SSELCG : 1;
			unsigned long SSELCH : 1;
			unsigned long  : 7;
			unsigned long CSTRT : 1;
#else
			unsigned long CSTRT : 1;
			unsigned long  : 7;
			unsigned long SSELCH : 1;
			unsigned long SSELCG : 1;
			unsigned long SSELCF : 1;
			unsigned long SSELCE : 1;
			unsigned long SSELCD : 1;
			unsigned long SSELCC : 1;
			unsigned long SSELCB : 1;
			unsigned long SSELCA : 1;
			unsigned long SSCBFAH : 1;
			unsigned long SSCBFAL : 1;
			unsigned long SSCBRAH : 1;
			unsigned long SSCBRAL : 1;
			unsigned long SSCAFBH : 1;
			unsigned long SSCAFBL : 1;
			unsigned long SSCARBH : 1;
			unsigned long SSCARBL : 1;
			unsigned long SSGTRGDF : 1;
			unsigned long SSGTRGDR : 1;
			unsigned long SSGTRGCF : 1;
			unsigned long SSGTRGCR : 1;
			unsigned long SSGTRGBF : 1;
			unsigned long SSGTRGBR : 1;
			unsigned long SSGTRGAF : 1;
			unsigned long SSGTRGAR : 1;
#endif
	} BIT;
	} GTSSR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PSGTRGAR : 1;
			unsigned long PSGTRGAF : 1;
			unsigned long PSGTRGBR : 1;
			unsigned long PSGTRGBF : 1;
			unsigned long PSGTRGCR : 1;
			unsigned long PSGTRGCF : 1;
			unsigned long PSGTRGDR : 1;
			unsigned long PSGTRGDF : 1;
			unsigned long PSCARBL : 1;
			unsigned long PSCARBH : 1;
			unsigned long PSCAFBL : 1;
			unsigned long PSCAFBH : 1;
			unsigned long PSCBRAL : 1;
			unsigned long PSCBRAH : 1;
			unsigned long PSCBFAL : 1;
			unsigned long PSCBFAH : 1;
			unsigned long PSELCA : 1;
			unsigned long PSELCB : 1;
			unsigned long PSELCC : 1;
			unsigned long PSELCD : 1;
			unsigned long PSELCE : 1;
			unsigned long PSELCF : 1;
			unsigned long PSELCG : 1;
			unsigned long PSELCH : 1;
			unsigned long  : 7;
			unsigned long CSTOP : 1;
#else
			unsigned long CSTOP : 1;
			unsigned long  : 7;
			unsigned long PSELCH : 1;
			unsigned long PSELCG : 1;
			unsigned long PSELCF : 1;
			unsigned long PSELCE : 1;
			unsigned long PSELCD : 1;
			unsigned long PSELCC : 1;
			unsigned long PSELCB : 1;
			unsigned long PSELCA : 1;
			unsigned long PSCBFAH : 1;
			unsigned long PSCBFAL : 1;
			unsigned long PSCBRAH : 1;
			unsigned long PSCBRAL : 1;
			unsigned long PSCAFBH : 1;
			unsigned long PSCAFBL : 1;
			unsigned long PSCARBH : 1;
			unsigned long PSCARBL : 1;
			unsigned long PSGTRGDF : 1;
			unsigned long PSGTRGDR : 1;
			unsigned long PSGTRGCF : 1;
			unsigned long PSGTRGCR : 1;
			unsigned long PSGTRGBF : 1;
			unsigned long PSGTRGBR : 1;
			unsigned long PSGTRGAF : 1;
			unsigned long PSGTRGAR : 1;
#endif
	} BIT;
	} GTPSR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CSGTRGAR : 1;
			unsigned long CSGTRGAF : 1;
			unsigned long CSGTRGBR : 1;
			unsigned long CSGTRGBF : 1;
			unsigned long CSGTRGCR : 1;
			unsigned long CSGTRGCF : 1;
			unsigned long CSGTRGDR : 1;
			unsigned long CSGTRGDF : 1;
			unsigned long CSCARBL : 1;
			unsigned long CSCARBH : 1;
			unsigned long CSCAFBL : 1;
			unsigned long CSCAFBH : 1;
			unsigned long CSCBRAL : 1;
			unsigned long CSCBRAH : 1;
			unsigned long CSCBFAL : 1;
			unsigned long CSCBFAH : 1;
			unsigned long CSELCA : 1;
			unsigned long CSELCB : 1;
			unsigned long CSELCC : 1;
			unsigned long CSELCD : 1;
			unsigned long CSELCE : 1;
			unsigned long CSELCF : 1;
			unsigned long CSELCG : 1;
			unsigned long CSELCH : 1;
			unsigned long  : 7;
			unsigned long CCLR : 1;
#else
			unsigned long CCLR : 1;
			unsigned long  : 7;
			unsigned long CSELCH : 1;
			unsigned long CSELCG : 1;
			unsigned long CSELCF : 1;
			unsigned long CSELCE : 1;
			unsigned long CSELCD : 1;
			unsigned long CSELCC : 1;
			unsigned long CSELCB : 1;
			unsigned long CSELCA : 1;
			unsigned long CSCBFAH : 1;
			unsigned long CSCBFAL : 1;
			unsigned long CSCBRAH : 1;
			unsigned long CSCBRAL : 1;
			unsigned long CSCAFBH : 1;
			unsigned long CSCAFBL : 1;
			unsigned long CSCARBH : 1;
			unsigned long CSCARBL : 1;
			unsigned long CSGTRGDF : 1;
			unsigned long CSGTRGDR : 1;
			unsigned long CSGTRGCF : 1;
			unsigned long CSGTRGCR : 1;
			unsigned long CSGTRGBF : 1;
			unsigned long CSGTRGBR : 1;
			unsigned long CSGTRGAF : 1;
			unsigned long CSGTRGAR : 1;
#endif
	} BIT;
	} GTCSR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long USGTRGAR : 1;
			unsigned long USGTRGAF : 1;
			unsigned long USGTRGBR : 1;
			unsigned long USGTRGBF : 1;
			unsigned long USGTRGCR : 1;
			unsigned long USGTRGCF : 1;
			unsigned long USGTRGDR : 1;
			unsigned long USGTRGDF : 1;
			unsigned long USCARBL : 1;
			unsigned long USCARBH : 1;
			unsigned long USCAFBL : 1;
			unsigned long USCAFBH : 1;
			unsigned long USCBRAL : 1;
			unsigned long USCBRAH : 1;
			unsigned long USCBFAL : 1;
			unsigned long USCBFAH : 1;
			unsigned long USELCA : 1;
			unsigned long USELCB : 1;
			unsigned long USELCC : 1;
			unsigned long USELCD : 1;
			unsigned long USELCE : 1;
			unsigned long USELCF : 1;
			unsigned long USELCG : 1;
			unsigned long USELCH : 1;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long USELCH : 1;
			unsigned long USELCG : 1;
			unsigned long USELCF : 1;
			unsigned long USELCE : 1;
			unsigned long USELCD : 1;
			unsigned long USELCC : 1;
			unsigned long USELCB : 1;
			unsigned long USELCA : 1;
			unsigned long USCBFAH : 1;
			unsigned long USCBFAL : 1;
			unsigned long USCBRAH : 1;
			unsigned long USCBRAL : 1;
			unsigned long USCAFBH : 1;
			unsigned long USCAFBL : 1;
			unsigned long USCARBH : 1;
			unsigned long USCARBL : 1;
			unsigned long USGTRGDF : 1;
			unsigned long USGTRGDR : 1;
			unsigned long USGTRGCF : 1;
			unsigned long USGTRGCR : 1;
			unsigned long USGTRGBF : 1;
			unsigned long USGTRGBR : 1;
			unsigned long USGTRGAF : 1;
			unsigned long USGTRGAR : 1;
#endif
	} BIT;
	} GTUPSR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long DSGTRGAR : 1;
			unsigned long DSGTRGAF : 1;
			unsigned long DSGTRGBR : 1;
			unsigned long DSGTRGBF : 1;
			unsigned long DSGTRGCR : 1;
			unsigned long DSGTRGCF : 1;
			unsigned long DSGTRGDR : 1;
			unsigned long DSGTRGDF : 1;
			unsigned long DSCARBL : 1;
			unsigned long DSCARBH : 1;
			unsigned long DSCAFBL : 1;
			unsigned long DSCAFBH : 1;
			unsigned long DSCBRAL : 1;
			unsigned long DSCBRAH : 1;
			unsigned long DSCBFAL : 1;
			unsigned long DSCBFAH : 1;
			unsigned long DSELCA : 1;
			unsigned long DSELCB : 1;
			unsigned long DSELCC : 1;
			unsigned long DSELCD : 1;
			unsigned long DSELCE : 1;
			unsigned long DSELCF : 1;
			unsigned long DSELCG : 1;
			unsigned long DSELCH : 1;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long DSELCH : 1;
			unsigned long DSELCG : 1;
			unsigned long DSELCF : 1;
			unsigned long DSELCE : 1;
			unsigned long DSELCD : 1;
			unsigned long DSELCC : 1;
			unsigned long DSELCB : 1;
			unsigned long DSELCA : 1;
			unsigned long DSCBFAH : 1;
			unsigned long DSCBFAL : 1;
			unsigned long DSCBRAH : 1;
			unsigned long DSCBRAL : 1;
			unsigned long DSCAFBH : 1;
			unsigned long DSCAFBL : 1;
			unsigned long DSCARBH : 1;
			unsigned long DSCARBL : 1;
			unsigned long DSGTRGDF : 1;
			unsigned long DSGTRGDR : 1;
			unsigned long DSGTRGCF : 1;
			unsigned long DSGTRGCR : 1;
			unsigned long DSGTRGBF : 1;
			unsigned long DSGTRGBR : 1;
			unsigned long DSGTRGAF : 1;
			unsigned long DSGTRGAR : 1;
#endif
	} BIT;
	} GTDNSR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ASGTRGAR : 1;
			unsigned long ASGTRGAF : 1;
			unsigned long ASGTRGBR : 1;
			unsigned long ASGTRGBF : 1;
			unsigned long ASGTRGCR : 1;
			unsigned long ASGTRGCF : 1;
			unsigned long ASGTRGDR : 1;
			unsigned long ASGTRGDF : 1;
			unsigned long ASCARBL : 1;
			unsigned long ASCARBH : 1;
			unsigned long ASCAFBL : 1;
			unsigned long ASCAFBH : 1;
			unsigned long ASCBRAL : 1;
			unsigned long ASCBRAH : 1;
			unsigned long ASCBFAL : 1;
			unsigned long ASCBFAH : 1;
			unsigned long ASELCA : 1;
			unsigned long ASELCB : 1;
			unsigned long ASELCC : 1;
			unsigned long ASELCD : 1;
			unsigned long ASELCE : 1;
			unsigned long ASELCF : 1;
			unsigned long ASELCG : 1;
			unsigned long ASELCH : 1;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long ASELCH : 1;
			unsigned long ASELCG : 1;
			unsigned long ASELCF : 1;
			unsigned long ASELCE : 1;
			unsigned long ASELCD : 1;
			unsigned long ASELCC : 1;
			unsigned long ASELCB : 1;
			unsigned long ASELCA : 1;
			unsigned long ASCBFAH : 1;
			unsigned long ASCBFAL : 1;
			unsigned long ASCBRAH : 1;
			unsigned long ASCBRAL : 1;
			unsigned long ASCAFBH : 1;
			unsigned long ASCAFBL : 1;
			unsigned long ASCARBH : 1;
			unsigned long ASCARBL : 1;
			unsigned long ASGTRGDF : 1;
			unsigned long ASGTRGDR : 1;
			unsigned long ASGTRGCF : 1;
			unsigned long ASGTRGCR : 1;
			unsigned long ASGTRGBF : 1;
			unsigned long ASGTRGBR : 1;
			unsigned long ASGTRGAF : 1;
			unsigned long ASGTRGAR : 1;
#endif
	} BIT;
	} GTICASR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long BSGTRGAR : 1;
			unsigned long BSGTRGAF : 1;
			unsigned long BSGTRGBR : 1;
			unsigned long BSGTRGBF : 1;
			unsigned long BSGTRGCR : 1;
			unsigned long BSGTRGCF : 1;
			unsigned long BSGTRGDR : 1;
			unsigned long BSGTRGDF : 1;
			unsigned long BSCARBL : 1;
			unsigned long BSCARBH : 1;
			unsigned long BSCAFBL : 1;
			unsigned long BSCAFBH : 1;
			unsigned long BSCBRAL : 1;
			unsigned long BSCBRAH : 1;
			unsigned long BSCBFAL : 1;
			unsigned long BSCBFAH : 1;
			unsigned long BSELCA : 1;
			unsigned long BSELCB : 1;
			unsigned long BSELCC : 1;
			unsigned long BSELCD : 1;
			unsigned long BSELCE : 1;
			unsigned long BSELCF : 1;
			unsigned long BSELCG : 1;
			unsigned long BSELCH : 1;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long BSELCH : 1;
			unsigned long BSELCG : 1;
			unsigned long BSELCF : 1;
			unsigned long BSELCE : 1;
			unsigned long BSELCD : 1;
			unsigned long BSELCC : 1;
			unsigned long BSELCB : 1;
			unsigned long BSELCA : 1;
			unsigned long BSCBFAH : 1;
			unsigned long BSCBFAL : 1;
			unsigned long BSCBRAH : 1;
			unsigned long BSCBRAL : 1;
			unsigned long BSCAFBH : 1;
			unsigned long BSCAFBL : 1;
			unsigned long BSCARBH : 1;
			unsigned long BSCARBL : 1;
			unsigned long BSGTRGDF : 1;
			unsigned long BSGTRGDR : 1;
			unsigned long BSGTRGCF : 1;
			unsigned long BSGTRGCR : 1;
			unsigned long BSGTRGBF : 1;
			unsigned long BSGTRGBR : 1;
			unsigned long BSGTRGAF : 1;
			unsigned long BSGTRGAR : 1;
#endif
	} BIT;
	} GTICBSR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CST : 1;
			unsigned long  : 7;
			unsigned long ICDS : 1;
			unsigned long  : 7;
			unsigned long MD : 3;
			unsigned long  : 4;
			unsigned long TPCS : 4;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long TPCS : 4;
			unsigned long  : 4;
			unsigned long MD : 3;
			unsigned long  : 7;
			unsigned long ICDS : 1;
			unsigned long  : 7;
			unsigned long CST : 1;
#endif
	} BIT;
	} GTCR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long UD : 1;
			unsigned long UDF : 1;
			unsigned long  : 14;
			unsigned long OADTY : 2;
			unsigned long OADTYF : 1;
			unsigned long OADTYR : 1;
			unsigned long  : 4;
			unsigned long OBDTY : 2;
			unsigned long OBDTYF : 1;
			unsigned long OBDTYR : 1;
			unsigned long  : 4;
#else
			unsigned long  : 4;
			unsigned long OBDTYR : 1;
			unsigned long OBDTYF : 1;
			unsigned long OBDTY : 2;
			unsigned long  : 4;
			unsigned long OADTYR : 1;
			unsigned long OADTYF : 1;
			unsigned long OADTY : 2;
			unsigned long  : 14;
			unsigned long UDF : 1;
			unsigned long UD : 1;
#endif
	} BIT;
	} GTUDDTYC;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GTIOA : 5;
			unsigned long  : 1;
			unsigned long OADFLT : 1;
			unsigned long OAHLD : 1;
			unsigned long OAE : 1;
			unsigned long OADF : 2;
			unsigned long  : 2;
			unsigned long NFAEN : 1;
			unsigned long NFCSA : 2;
			unsigned long GTIOB : 5;
			unsigned long  : 1;
			unsigned long OBDFLT : 1;
			unsigned long OBHLD : 1;
			unsigned long OBE : 1;
			unsigned long OBDF : 2;
			unsigned long  : 2;
			unsigned long NFBEN : 1;
			unsigned long NFCSB : 2;
#else
			unsigned long NFCSB : 2;
			unsigned long NFBEN : 1;
			unsigned long  : 2;
			unsigned long OBDF : 2;
			unsigned long OBE : 1;
			unsigned long OBHLD : 1;
			unsigned long OBDFLT : 1;
			unsigned long  : 1;
			unsigned long GTIOB : 5;
			unsigned long NFCSA : 2;
			unsigned long NFAEN : 1;
			unsigned long  : 2;
			unsigned long OADF : 2;
			unsigned long OAE : 1;
			unsigned long OAHLD : 1;
			unsigned long OADFLT : 1;
			unsigned long  : 1;
			unsigned long GTIOA : 5;
#endif
	} BIT;
	} GTIOR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long GTINTA : 1;
			unsigned long GTINTB : 1;
			unsigned long GTINTC : 1;
			unsigned long GTINTD : 1;
			unsigned long GTINTE : 1;
			unsigned long GTINTF : 1;
			unsigned long GTINTPR : 2;
			unsigned long  : 8;
			unsigned long ADTRAUEN : 1;
			unsigned long ADTRADEN : 1;
			unsigned long ADTRBUEN : 1;
			unsigned long ADTRBDEN : 1;
			unsigned long  : 4;
			unsigned long GRP : 2;
			unsigned long  : 2;
			unsigned long GRPDTE : 1;
			unsigned long GRPABH : 1;
			unsigned long GRPABL : 1;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long GRPABL : 1;
			unsigned long GRPABH : 1;
			unsigned long GRPDTE : 1;
			unsigned long  : 2;
			unsigned long GRP : 2;
			unsigned long  : 4;
			unsigned long ADTRBDEN : 1;
			unsigned long ADTRBUEN : 1;
			unsigned long ADTRADEN : 1;
			unsigned long ADTRAUEN : 1;
			unsigned long  : 8;
			unsigned long GTINTPR : 2;
			unsigned long GTINTF : 1;
			unsigned long GTINTE : 1;
			unsigned long GTINTD : 1;
			unsigned long GTINTC : 1;
			unsigned long GTINTB : 1;
			unsigned long GTINTA : 1;
#endif
	} BIT;
	} GTINTAD;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 8;
			unsigned long ITCNT : 3;
			unsigned long  : 4;
			unsigned long TUCF : 1;
			unsigned long ADTRAUF : 1;
			unsigned long ADTRADF : 1;
			unsigned long ADTRBUF : 1;
			unsigned long ADTRBDF : 1;
			unsigned long  : 4;
			unsigned long ODF : 1;
			unsigned long  : 3;
			unsigned long DTEF : 1;
			unsigned long OABHF : 1;
			unsigned long OABLF : 1;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long OABLF : 1;
			unsigned long OABHF : 1;
			unsigned long DTEF : 1;
			unsigned long  : 3;
			unsigned long ODF : 1;
			unsigned long  : 4;
			unsigned long ADTRBDF : 1;
			unsigned long ADTRBUF : 1;
			unsigned long ADTRADF : 1;
			unsigned long ADTRAUF : 1;
			unsigned long TUCF : 1;
			unsigned long  : 4;
			unsigned long ITCNT : 3;
			unsigned long  : 8;
#endif
	} BIT;
	} GTST;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long BD : 4;
			unsigned long  : 4;
			unsigned long DBRTECA : 1;
			unsigned long  : 1;
			unsigned long DBRTECB : 1;
			unsigned long  : 5;
			unsigned long CCRA : 2;
			unsigned long CCRB : 2;
			unsigned long PR : 2;
			unsigned long CCRSWT : 1;
			unsigned long  : 1;
			unsigned long ADTTA : 2;
			unsigned long ADTDA : 1;
			unsigned long  : 1;
			unsigned long ADTTB : 2;
			unsigned long ADTDB : 1;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long ADTDB : 1;
			unsigned long ADTTB : 2;
			unsigned long  : 1;
			unsigned long ADTDA : 1;
			unsigned long ADTTA : 2;
			unsigned long  : 1;
			unsigned long CCRSWT : 1;
			unsigned long PR : 2;
			unsigned long CCRB : 2;
			unsigned long CCRA : 2;
			unsigned long  : 5;
			unsigned long DBRTECB : 1;
			unsigned long  : 1;
			unsigned long DBRTECA : 1;
			unsigned long  : 4;
			unsigned long BD : 4;
#endif
	} BIT;
	} GTBER;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ITLA : 1;
			unsigned long ITLB : 1;
			unsigned long ITLC : 1;
			unsigned long ITLD : 1;
			unsigned long ITLE : 1;
			unsigned long ITLF : 1;
			unsigned long IVTC : 2;
			unsigned long IVTT : 3;
			unsigned long  : 1;
			unsigned long ADTAL : 1;
			unsigned long  : 1;
			unsigned long ADTBL : 1;
			unsigned long  : 17;
#else
			unsigned long  : 17;
			unsigned long ADTBL : 1;
			unsigned long  : 1;
			unsigned long ADTAL : 1;
			unsigned long  : 1;
			unsigned long IVTT : 3;
			unsigned long IVTC : 2;
			unsigned long ITLF : 1;
			unsigned long ITLE : 1;
			unsigned long ITLD : 1;
			unsigned long ITLC : 1;
			unsigned long ITLB : 1;
			unsigned long ITLA : 1;
#endif
	} BIT;
	} GTITC;
	unsigned long  GTCNT;
	unsigned long  GTCCRA;
	unsigned long  GTCCRB;
	unsigned long  GTCCRC;
	unsigned long  GTCCRE;
	unsigned long  GTCCRD;
	unsigned long  GTCCRF;
	unsigned long  GTPR;
	unsigned long  GTPBR;
	unsigned long  GTPDBR;
	unsigned long  GTADTRA;
	unsigned long  GTADTBRA;
	unsigned long  GTADTDBRA;
	unsigned long  GTADTRB;
	unsigned long  GTADTBRB;
	unsigned long  GTADTDBRB;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TDE : 1;
			unsigned long  : 3;
			unsigned long TDBUE : 1;
			unsigned long TDBDE : 1;
			unsigned long  : 2;
			unsigned long TDFER : 1;
			unsigned long  : 23;
#else
			unsigned long  : 23;
			unsigned long TDFER : 1;
			unsigned long  : 2;
			unsigned long TDBDE : 1;
			unsigned long TDBUE : 1;
			unsigned long  : 3;
			unsigned long TDE : 1;
#endif
	} BIT;
	} GTDTCR;
	unsigned long  GTDVU;
	unsigned long  GTDVD;
	unsigned long  GTDBU;
	unsigned long  GTDBD;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long SOS : 2;
			unsigned long  : 30;
#else
			unsigned long  : 30;
			unsigned long SOS : 2;
#endif
	} BIT;
	} GTSOS;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long SOTR : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long SOTR : 1;
#endif
	} BIT;
	} GTSOTR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long ADSMS0 : 2;
			unsigned long  : 6;
			unsigned long ADSMEN0 : 1;
			unsigned long  : 7;
			unsigned long ADSMS1 : 2;
			unsigned long  : 6;
			unsigned long ADSMEN1 : 1;
			unsigned long  : 7;
#else
			unsigned long  : 7;
			unsigned long ADSMEN1 : 1;
			unsigned long  : 6;
			unsigned long ADSMS1 : 2;
			unsigned long  : 7;
			unsigned long ADSMEN0 : 1;
			unsigned long  : 6;
			unsigned long ADSMS0 : 2;
#endif
	} BIT;
	} GTADSMR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EIVTC1 : 2;
			unsigned long  : 2;
			unsigned long EIVTT1 : 4;
			unsigned long  : 4;
			unsigned long EITCNT1 : 4;
			unsigned long EIVTC2 : 2;
			unsigned long  : 2;
			unsigned long EIVTT2 : 4;
			unsigned long EITCNT2IV : 4;
			unsigned long EITCNT2 : 4;
#else
			unsigned long EITCNT2 : 4;
			unsigned long EITCNT2IV : 4;
			unsigned long EIVTT2 : 4;
			unsigned long  : 2;
			unsigned long EIVTC2 : 2;
			unsigned long EITCNT1 : 4;
			unsigned long  : 4;
			unsigned long EIVTT1 : 4;
			unsigned long  : 2;
			unsigned long EIVTC1 : 2;
#endif
	} BIT;
	} GTEITC;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EITLA : 3;
			unsigned long  : 1;
			unsigned long EITLB : 3;
			unsigned long  : 1;
			unsigned long EITLC : 3;
			unsigned long  : 1;
			unsigned long EITLD : 3;
			unsigned long  : 1;
			unsigned long EITLE : 3;
			unsigned long  : 1;
			unsigned long EITLF : 3;
			unsigned long  : 1;
			unsigned long EITLV : 3;
			unsigned long  : 1;
			unsigned long EITLU : 3;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long EITLU : 3;
			unsigned long  : 1;
			unsigned long EITLV : 3;
			unsigned long  : 1;
			unsigned long EITLF : 3;
			unsigned long  : 1;
			unsigned long EITLE : 3;
			unsigned long  : 1;
			unsigned long EITLD : 3;
			unsigned long  : 1;
			unsigned long EITLC : 3;
			unsigned long  : 1;
			unsigned long EITLB : 3;
			unsigned long  : 1;
			unsigned long EITLA : 3;
#endif
	} BIT;
	} GTEITLI1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EADTAL : 3;
			unsigned long  : 1;
			unsigned long EADTBL : 3;
			unsigned long  : 25;
#else
			unsigned long  : 25;
			unsigned long EADTBL : 3;
			unsigned long  : 1;
			unsigned long EADTAL : 3;
#endif
	} BIT;
	} GTEITLI2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EBTLCA : 3;
			unsigned long  : 1;
			unsigned long EBTLCB : 3;
			unsigned long  : 1;
			unsigned long EBTLPR : 3;
			unsigned long  : 5;
			unsigned long EBTLADA : 3;
			unsigned long  : 1;
			unsigned long EBTLADB : 3;
			unsigned long  : 1;
			unsigned long EBTLDVU : 3;
			unsigned long  : 1;
			unsigned long EBTLDVD : 3;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long EBTLDVD : 3;
			unsigned long  : 1;
			unsigned long EBTLDVU : 3;
			unsigned long  : 1;
			unsigned long EBTLADB : 3;
			unsigned long  : 1;
			unsigned long EBTLADA : 3;
			unsigned long  : 5;
			unsigned long EBTLPR : 3;
			unsigned long  : 1;
			unsigned long EBTLCB : 3;
			unsigned long  : 1;
			unsigned long EBTLCA : 3;
#endif
	} BIT;
	} GTEITLB;
	char           wk0[24];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long SECSEL0 : 1;
			unsigned long SECSEL1 : 1;
			unsigned long SECSEL2 : 1;
			unsigned long SECSEL3 : 1;
			unsigned long  : 28;
#else
			unsigned long  : 28;
			unsigned long SECSEL3 : 1;
			unsigned long SECSEL2 : 1;
			unsigned long SECSEL1 : 1;
			unsigned long SECSEL0 : 1;
#endif
	} BIT;
	} GTSECSR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long SBDCE : 1;
			unsigned long SBDPE : 1;
			unsigned long SBDAE : 1;
			unsigned long SBDDE : 1;
			unsigned long  : 4;
			unsigned long SBDCD : 1;
			unsigned long SBDPD : 1;
			unsigned long SBDAD : 1;
			unsigned long SBDDD : 1;
			unsigned long  : 20;
#else
			unsigned long  : 20;
			unsigned long SBDDD : 1;
			unsigned long SBDAD : 1;
			unsigned long SBDPD : 1;
			unsigned long SBDCD : 1;
			unsigned long  : 4;
			unsigned long SBDDE : 1;
			unsigned long SBDAE : 1;
			unsigned long SBDPE : 1;
			unsigned long SBDCE : 1;
#endif
	} BIT;
	} GTSECR;
} st_gptw_t;

typedef struct st_icu {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IR : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char IR : 1;
#endif
	} BIT;
	} IR[256];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DTCE : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char DTCE : 1;
#endif
	} BIT;
	} DTCER[256];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IEN0 : 1;
			unsigned char IEN1 : 1;
			unsigned char IEN2 : 1;
			unsigned char IEN3 : 1;
			unsigned char IEN4 : 1;
			unsigned char IEN5 : 1;
			unsigned char IEN6 : 1;
			unsigned char IEN7 : 1;
#else
			unsigned char IEN7 : 1;
			unsigned char IEN6 : 1;
			unsigned char IEN5 : 1;
			unsigned char IEN4 : 1;
			unsigned char IEN3 : 1;
			unsigned char IEN2 : 1;
			unsigned char IEN1 : 1;
			unsigned char IEN0 : 1;
#endif
	} BIT;
	} IER[32];
	char           wk0[192];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SWINT : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char SWINT : 1;
#endif
	} BIT;
	} SWINTR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SWINT2 : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char SWINT2 : 1;
#endif
	} BIT;
	} SWINT2R;
	char           wk1[14];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short FVCT : 8;
			unsigned short  : 7;
			unsigned short FIEN : 1;
#else
			unsigned short FIEN : 1;
			unsigned short  : 7;
			unsigned short FVCT : 8;
#endif
	} BIT;
	} FIR;
	char           wk2[14];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IPR : 4;
			unsigned char  : 4;
#else
			unsigned char  : 4;
			unsigned char IPR : 4;
#endif
	} BIT;
	} IPR[256];
	unsigned char  DMRSR0;
	char           wk3[3];
	unsigned char  DMRSR1;
	char           wk4[3];
	unsigned char  DMRSR2;
	char           wk5[3];
	unsigned char  DMRSR3;
	char           wk6[3];
	unsigned char  DMRSR4;
	char           wk7[3];
	unsigned char  DMRSR5;
	char           wk8[3];
	unsigned char  DMRSR6;
	char           wk9[3];
	unsigned char  DMRSR7;
	char           wk10[227];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 2;
			unsigned char IRQMD : 2;
			unsigned char  : 4;
#else
			unsigned char  : 4;
			unsigned char IRQMD : 2;
			unsigned char  : 2;
#endif
	} BIT;
	} IRQCR[16];
	char           wk11[16];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char FLTEN0 : 1;
			unsigned char FLTEN1 : 1;
			unsigned char FLTEN2 : 1;
			unsigned char FLTEN3 : 1;
			unsigned char FLTEN4 : 1;
			unsigned char FLTEN5 : 1;
			unsigned char FLTEN6 : 1;
			unsigned char FLTEN7 : 1;
#else
			unsigned char FLTEN7 : 1;
			unsigned char FLTEN6 : 1;
			unsigned char FLTEN5 : 1;
			unsigned char FLTEN4 : 1;
			unsigned char FLTEN3 : 1;
			unsigned char FLTEN2 : 1;
			unsigned char FLTEN1 : 1;
			unsigned char FLTEN0 : 1;
#endif
	} BIT;
	} IRQFLTE0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char FLTEN8 : 1;
			unsigned char FLTEN9 : 1;
			unsigned char FLTEN10 : 1;
			unsigned char FLTEN11 : 1;
			unsigned char FLTEN12 : 1;
			unsigned char FLTEN13 : 1;
			unsigned char FLTEN14 : 1;
			unsigned char FLTEN15 : 1;
#else
			unsigned char FLTEN15 : 1;
			unsigned char FLTEN14 : 1;
			unsigned char FLTEN13 : 1;
			unsigned char FLTEN12 : 1;
			unsigned char FLTEN11 : 1;
			unsigned char FLTEN10 : 1;
			unsigned char FLTEN9 : 1;
			unsigned char FLTEN8 : 1;
#endif
	} BIT;
	} IRQFLTE1;
	char           wk12[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short FCLKSEL0 : 2;
			unsigned short FCLKSEL1 : 2;
			unsigned short FCLKSEL2 : 2;
			unsigned short FCLKSEL3 : 2;
			unsigned short FCLKSEL4 : 2;
			unsigned short FCLKSEL5 : 2;
			unsigned short FCLKSEL6 : 2;
			unsigned short FCLKSEL7 : 2;
#else
			unsigned short FCLKSEL7 : 2;
			unsigned short FCLKSEL6 : 2;
			unsigned short FCLKSEL5 : 2;
			unsigned short FCLKSEL4 : 2;
			unsigned short FCLKSEL3 : 2;
			unsigned short FCLKSEL2 : 2;
			unsigned short FCLKSEL1 : 2;
			unsigned short FCLKSEL0 : 2;
#endif
	} BIT;
	} IRQFLTC0;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short FCLKSEL8 : 2;
			unsigned short FCLKSEL9 : 2;
			unsigned short FCLKSEL10 : 2;
			unsigned short FCLKSEL11 : 2;
			unsigned short FCLKSEL12 : 2;
			unsigned short FCLKSEL13 : 2;
			unsigned short FCLKSEL14 : 2;
			unsigned short FCLKSEL15 : 2;
#else
			unsigned short FCLKSEL15 : 2;
			unsigned short FCLKSEL14 : 2;
			unsigned short FCLKSEL13 : 2;
			unsigned short FCLKSEL12 : 2;
			unsigned short FCLKSEL11 : 2;
			unsigned short FCLKSEL10 : 2;
			unsigned short FCLKSEL9 : 2;
			unsigned short FCLKSEL8 : 2;
#endif
	} BIT;
	} IRQFLTC1;
	char           wk13[84];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NMIST : 1;
			unsigned char OSTST : 1;
			unsigned char WDTST : 1;
			unsigned char IWDTST : 1;
			unsigned char LVD1ST : 1;
			unsigned char LVD2ST : 1;
			unsigned char EXNMIST : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char EXNMIST : 1;
			unsigned char LVD2ST : 1;
			unsigned char LVD1ST : 1;
			unsigned char IWDTST : 1;
			unsigned char WDTST : 1;
			unsigned char OSTST : 1;
			unsigned char NMIST : 1;
#endif
	} BIT;
	} NMISR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NMIEN : 1;
			unsigned char OSTEN : 1;
			unsigned char WDTEN : 1;
			unsigned char IWDTEN : 1;
			unsigned char LVD1EN : 1;
			unsigned char LVD2EN : 1;
			unsigned char EXNMIEN : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char EXNMIEN : 1;
			unsigned char LVD2EN : 1;
			unsigned char LVD1EN : 1;
			unsigned char IWDTEN : 1;
			unsigned char WDTEN : 1;
			unsigned char OSTEN : 1;
			unsigned char NMIEN : 1;
#endif
	} BIT;
	} NMIER;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NMICLR : 1;
			unsigned char OSTCLR : 1;
			unsigned char WDTCLR : 1;
			unsigned char IWDTCLR : 1;
			unsigned char LVD1CLR : 1;
			unsigned char LVD2CLR : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char LVD2CLR : 1;
			unsigned char LVD1CLR : 1;
			unsigned char IWDTCLR : 1;
			unsigned char WDTCLR : 1;
			unsigned char OSTCLR : 1;
			unsigned char NMICLR : 1;
#endif
	} BIT;
	} NMICLR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 3;
			unsigned char NMIMD : 1;
			unsigned char  : 4;
#else
			unsigned char  : 4;
			unsigned char NMIMD : 1;
			unsigned char  : 3;
#endif
	} BIT;
	} NMICR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char RAMST : 1;
			unsigned char DPFPUST : 1;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char DPFPUST : 1;
			unsigned char RAMST : 1;
#endif
	} BIT;
	} EXNMISR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char RAMEN : 1;
			unsigned char DPFPUEN : 1;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char DPFPUEN : 1;
			unsigned char RAMEN : 1;
#endif
	} BIT;
	} EXNMIER;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 1;
			unsigned char DPFPUCLR : 1;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char DPFPUCLR : 1;
			unsigned char  : 1;
#endif
	} BIT;
	} EXNMICLR;
	char           wk14[9];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFLTEN : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char NFLTEN : 1;
#endif
	} BIT;
	} NMIFLTE;
	char           wk15[3];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFCLKSEL : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char NFCLKSEL : 2;
#endif
	} BIT;
	} NMIFLTC;
	char           wk16[27];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long IS0 : 1;
			unsigned long IS1 : 1;
			unsigned long IS2 : 1;
			unsigned long IS3 : 1;
			unsigned long IS4 : 1;
			unsigned long IS5 : 1;
			unsigned long IS6 : 1;
			unsigned long IS7 : 1;
			unsigned long IS8 : 1;
			unsigned long IS9 : 1;
			unsigned long IS10 : 1;
			unsigned long IS11 : 1;
			unsigned long IS12 : 1;
			unsigned long IS13 : 1;
			unsigned long IS14 : 1;
			unsigned long IS15 : 1;
			unsigned long IS16 : 1;
			unsigned long IS17 : 1;
			unsigned long IS18 : 1;
			unsigned long IS19 : 1;
			unsigned long IS20 : 1;
			unsigned long IS21 : 1;
			unsigned long IS22 : 1;
			unsigned long IS23 : 1;
			unsigned long IS24 : 1;
			unsigned long IS25 : 1;
			unsigned long IS26 : 1;
			unsigned long IS27 : 1;
			unsigned long IS28 : 1;
			unsigned long IS29 : 1;
			unsigned long IS30 : 1;
			unsigned long IS31 : 1;
#else
			unsigned long IS31 : 1;
			unsigned long IS30 : 1;
			unsigned long IS29 : 1;
			unsigned long IS28 : 1;
			unsigned long IS27 : 1;
			unsigned long IS26 : 1;
			unsigned long IS25 : 1;
			unsigned long IS24 : 1;
			unsigned long IS23 : 1;
			unsigned long IS22 : 1;
			unsigned long IS21 : 1;
			unsigned long IS20 : 1;
			unsigned long IS19 : 1;
			unsigned long IS18 : 1;
			unsigned long IS17 : 1;
			unsigned long IS16 : 1;
			unsigned long IS15 : 1;
			unsigned long IS14 : 1;
			unsigned long IS13 : 1;
			unsigned long IS12 : 1;
			unsigned long IS11 : 1;
			unsigned long IS10 : 1;
			unsigned long IS9 : 1;
			unsigned long IS8 : 1;
			unsigned long IS7 : 1;
			unsigned long IS6 : 1;
			unsigned long IS5 : 1;
			unsigned long IS4 : 1;
			unsigned long IS3 : 1;
			unsigned long IS2 : 1;
			unsigned long IS1 : 1;
			unsigned long IS0 : 1;
#endif
	} BIT;
	} GRPIE0;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EN0 : 1;
			unsigned long EN1 : 1;
			unsigned long EN2 : 1;
			unsigned long EN3 : 1;
			unsigned long EN4 : 1;
			unsigned long EN5 : 1;
			unsigned long EN6 : 1;
			unsigned long EN7 : 1;
			unsigned long EN8 : 1;
			unsigned long EN9 : 1;
			unsigned long EN10 : 1;
			unsigned long EN11 : 1;
			unsigned long EN12 : 1;
			unsigned long EN13 : 1;
			unsigned long EN14 : 1;
			unsigned long EN15 : 1;
			unsigned long EN16 : 1;
			unsigned long EN17 : 1;
			unsigned long EN18 : 1;
			unsigned long EN19 : 1;
			unsigned long EN20 : 1;
			unsigned long EN21 : 1;
			unsigned long EN22 : 1;
			unsigned long EN23 : 1;
			unsigned long EN24 : 1;
			unsigned long EN25 : 1;
			unsigned long EN26 : 1;
			unsigned long EN27 : 1;
			unsigned long EN28 : 1;
			unsigned long EN29 : 1;
			unsigned long EN30 : 1;
			unsigned long EN31 : 1;
#else
			unsigned long EN31 : 1;
			unsigned long EN30 : 1;
			unsigned long EN29 : 1;
			unsigned long EN28 : 1;
			unsigned long EN27 : 1;
			unsigned long EN26 : 1;
			unsigned long EN25 : 1;
			unsigned long EN24 : 1;
			unsigned long EN23 : 1;
			unsigned long EN22 : 1;
			unsigned long EN21 : 1;
			unsigned long EN20 : 1;
			unsigned long EN19 : 1;
			unsigned long EN18 : 1;
			unsigned long EN17 : 1;
			unsigned long EN16 : 1;
			unsigned long EN15 : 1;
			unsigned long EN14 : 1;
			unsigned long EN13 : 1;
			unsigned long EN12 : 1;
			unsigned long EN11 : 1;
			unsigned long EN10 : 1;
			unsigned long EN9 : 1;
			unsigned long EN8 : 1;
			unsigned long EN7 : 1;
			unsigned long EN6 : 1;
			unsigned long EN5 : 1;
			unsigned long EN4 : 1;
			unsigned long EN3 : 1;
			unsigned long EN2 : 1;
			unsigned long EN1 : 1;
			unsigned long EN0 : 1;
#endif
	} BIT;
	} GENIE0;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CLR0 : 1;
			unsigned long CLR1 : 1;
			unsigned long CLR2 : 1;
			unsigned long CLR3 : 1;
			unsigned long CLR4 : 1;
			unsigned long CLR5 : 1;
			unsigned long CLR6 : 1;
			unsigned long CLR7 : 1;
			unsigned long CLR8 : 1;
			unsigned long CLR9 : 1;
			unsigned long CLR10 : 1;
			unsigned long CLR11 : 1;
			unsigned long CLR12 : 1;
			unsigned long CLR13 : 1;
			unsigned long CLR14 : 1;
			unsigned long CLR15 : 1;
			unsigned long CLR16 : 1;
			unsigned long CLR17 : 1;
			unsigned long CLR18 : 1;
			unsigned long CLR19 : 1;
			unsigned long CLR20 : 1;
			unsigned long CLR21 : 1;
			unsigned long CLR22 : 1;
			unsigned long CLR23 : 1;
			unsigned long CLR24 : 1;
			unsigned long CLR25 : 1;
			unsigned long CLR26 : 1;
			unsigned long CLR27 : 1;
			unsigned long CLR28 : 1;
			unsigned long CLR29 : 1;
			unsigned long CLR30 : 1;
			unsigned long CLR31 : 1;
#else
			unsigned long CLR31 : 1;
			unsigned long CLR30 : 1;
			unsigned long CLR29 : 1;
			unsigned long CLR28 : 1;
			unsigned long CLR27 : 1;
			unsigned long CLR26 : 1;
			unsigned long CLR25 : 1;
			unsigned long CLR24 : 1;
			unsigned long CLR23 : 1;
			unsigned long CLR22 : 1;
			unsigned long CLR21 : 1;
			unsigned long CLR20 : 1;
			unsigned long CLR19 : 1;
			unsigned long CLR18 : 1;
			unsigned long CLR17 : 1;
			unsigned long CLR16 : 1;
			unsigned long CLR15 : 1;
			unsigned long CLR14 : 1;
			unsigned long CLR13 : 1;
			unsigned long CLR12 : 1;
			unsigned long CLR11 : 1;
			unsigned long CLR10 : 1;
			unsigned long CLR9 : 1;
			unsigned long CLR8 : 1;
			unsigned long CLR7 : 1;
			unsigned long CLR6 : 1;
			unsigned long CLR5 : 1;
			unsigned long CLR4 : 1;
			unsigned long CLR3 : 1;
			unsigned long CLR2 : 1;
			unsigned long CLR1 : 1;
			unsigned long CLR0 : 1;
#endif
	} BIT;
	} GCRIE0;
	char           wk17[68];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long IS0 : 1;
			unsigned long IS1 : 1;
			unsigned long IS2 : 1;
			unsigned long IS3 : 1;
			unsigned long IS4 : 1;
			unsigned long IS5 : 1;
			unsigned long IS6 : 1;
			unsigned long IS7 : 1;
			unsigned long IS8 : 1;
			unsigned long IS9 : 1;
			unsigned long IS10 : 1;
			unsigned long IS11 : 1;
			unsigned long IS12 : 1;
			unsigned long IS13 : 1;
			unsigned long IS14 : 1;
			unsigned long IS15 : 1;
			unsigned long IS16 : 1;
			unsigned long IS17 : 1;
			unsigned long IS18 : 1;
			unsigned long IS19 : 1;
			unsigned long IS20 : 1;
			unsigned long IS21 : 1;
			unsigned long IS22 : 1;
			unsigned long IS23 : 1;
			unsigned long IS24 : 1;
			unsigned long IS25 : 1;
			unsigned long IS26 : 1;
			unsigned long IS27 : 1;
			unsigned long IS28 : 1;
			unsigned long IS29 : 1;
			unsigned long IS30 : 1;
			unsigned long IS31 : 1;
#else
			unsigned long IS31 : 1;
			unsigned long IS30 : 1;
			unsigned long IS29 : 1;
			unsigned long IS28 : 1;
			unsigned long IS27 : 1;
			unsigned long IS26 : 1;
			unsigned long IS25 : 1;
			unsigned long IS24 : 1;
			unsigned long IS23 : 1;
			unsigned long IS22 : 1;
			unsigned long IS21 : 1;
			unsigned long IS20 : 1;
			unsigned long IS19 : 1;
			unsigned long IS18 : 1;
			unsigned long IS17 : 1;
			unsigned long IS16 : 1;
			unsigned long IS15 : 1;
			unsigned long IS14 : 1;
			unsigned long IS13 : 1;
			unsigned long IS12 : 1;
			unsigned long IS11 : 1;
			unsigned long IS10 : 1;
			unsigned long IS9 : 1;
			unsigned long IS8 : 1;
			unsigned long IS7 : 1;
			unsigned long IS6 : 1;
			unsigned long IS5 : 1;
			unsigned long IS4 : 1;
			unsigned long IS3 : 1;
			unsigned long IS2 : 1;
			unsigned long IS1 : 1;
			unsigned long IS0 : 1;
#endif
	} BIT;
	} GRPBE0;
	char           wk18[44];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long IS0 : 1;
			unsigned long IS1 : 1;
			unsigned long IS2 : 1;
			unsigned long IS3 : 1;
			unsigned long IS4 : 1;
			unsigned long IS5 : 1;
			unsigned long IS6 : 1;
			unsigned long IS7 : 1;
			unsigned long IS8 : 1;
			unsigned long IS9 : 1;
			unsigned long IS10 : 1;
			unsigned long IS11 : 1;
			unsigned long IS12 : 1;
			unsigned long IS13 : 1;
			unsigned long IS14 : 1;
			unsigned long IS15 : 1;
			unsigned long IS16 : 1;
			unsigned long IS17 : 1;
			unsigned long IS18 : 1;
			unsigned long IS19 : 1;
			unsigned long IS20 : 1;
			unsigned long IS21 : 1;
			unsigned long IS22 : 1;
			unsigned long IS23 : 1;
			unsigned long IS24 : 1;
			unsigned long IS25 : 1;
			unsigned long IS26 : 1;
			unsigned long IS27 : 1;
			unsigned long IS28 : 1;
			unsigned long IS29 : 1;
			unsigned long IS30 : 1;
			unsigned long IS31 : 1;
#else
			unsigned long IS31 : 1;
			unsigned long IS30 : 1;
			unsigned long IS29 : 1;
			unsigned long IS28 : 1;
			unsigned long IS27 : 1;
			unsigned long IS26 : 1;
			unsigned long IS25 : 1;
			unsigned long IS24 : 1;
			unsigned long IS23 : 1;
			unsigned long IS22 : 1;
			unsigned long IS21 : 1;
			unsigned long IS20 : 1;
			unsigned long IS19 : 1;
			unsigned long IS18 : 1;
			unsigned long IS17 : 1;
			unsigned long IS16 : 1;
			unsigned long IS15 : 1;
			unsigned long IS14 : 1;
			unsigned long IS13 : 1;
			unsigned long IS12 : 1;
			unsigned long IS11 : 1;
			unsigned long IS10 : 1;
			unsigned long IS9 : 1;
			unsigned long IS8 : 1;
			unsigned long IS7 : 1;
			unsigned long IS6 : 1;
			unsigned long IS5 : 1;
			unsigned long IS4 : 1;
			unsigned long IS3 : 1;
			unsigned long IS2 : 1;
			unsigned long IS1 : 1;
			unsigned long IS0 : 1;
#endif
	} BIT;
	} GRPBL0;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long IS0 : 1;
			unsigned long IS1 : 1;
			unsigned long IS2 : 1;
			unsigned long IS3 : 1;
			unsigned long IS4 : 1;
			unsigned long IS5 : 1;
			unsigned long IS6 : 1;
			unsigned long IS7 : 1;
			unsigned long IS8 : 1;
			unsigned long IS9 : 1;
			unsigned long IS10 : 1;
			unsigned long IS11 : 1;
			unsigned long IS12 : 1;
			unsigned long IS13 : 1;
			unsigned long IS14 : 1;
			unsigned long IS15 : 1;
			unsigned long IS16 : 1;
			unsigned long IS17 : 1;
			unsigned long IS18 : 1;
			unsigned long IS19 : 1;
			unsigned long IS20 : 1;
			unsigned long IS21 : 1;
			unsigned long IS22 : 1;
			unsigned long IS23 : 1;
			unsigned long IS24 : 1;
			unsigned long IS25 : 1;
			unsigned long IS26 : 1;
			unsigned long IS27 : 1;
			unsigned long IS28 : 1;
			unsigned long IS29 : 1;
			unsigned long IS30 : 1;
			unsigned long IS31 : 1;
#else
			unsigned long IS31 : 1;
			unsigned long IS30 : 1;
			unsigned long IS29 : 1;
			unsigned long IS28 : 1;
			unsigned long IS27 : 1;
			unsigned long IS26 : 1;
			unsigned long IS25 : 1;
			unsigned long IS24 : 1;
			unsigned long IS23 : 1;
			unsigned long IS22 : 1;
			unsigned long IS21 : 1;
			unsigned long IS20 : 1;
			unsigned long IS19 : 1;
			unsigned long IS18 : 1;
			unsigned long IS17 : 1;
			unsigned long IS16 : 1;
			unsigned long IS15 : 1;
			unsigned long IS14 : 1;
			unsigned long IS13 : 1;
			unsigned long IS12 : 1;
			unsigned long IS11 : 1;
			unsigned long IS10 : 1;
			unsigned long IS9 : 1;
			unsigned long IS8 : 1;
			unsigned long IS7 : 1;
			unsigned long IS6 : 1;
			unsigned long IS5 : 1;
			unsigned long IS4 : 1;
			unsigned long IS3 : 1;
			unsigned long IS2 : 1;
			unsigned long IS1 : 1;
			unsigned long IS0 : 1;
#endif
	} BIT;
	} GRPBL1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long IS0 : 1;
			unsigned long IS1 : 1;
			unsigned long IS2 : 1;
			unsigned long IS3 : 1;
			unsigned long IS4 : 1;
			unsigned long IS5 : 1;
			unsigned long IS6 : 1;
			unsigned long IS7 : 1;
			unsigned long IS8 : 1;
			unsigned long IS9 : 1;
			unsigned long IS10 : 1;
			unsigned long IS11 : 1;
			unsigned long IS12 : 1;
			unsigned long IS13 : 1;
			unsigned long IS14 : 1;
			unsigned long IS15 : 1;
			unsigned long IS16 : 1;
			unsigned long IS17 : 1;
			unsigned long IS18 : 1;
			unsigned long IS19 : 1;
			unsigned long IS20 : 1;
			unsigned long IS21 : 1;
			unsigned long IS22 : 1;
			unsigned long IS23 : 1;
			unsigned long IS24 : 1;
			unsigned long IS25 : 1;
			unsigned long IS26 : 1;
			unsigned long IS27 : 1;
			unsigned long IS28 : 1;
			unsigned long IS29 : 1;
			unsigned long IS30 : 1;
			unsigned long IS31 : 1;
#else
			unsigned long IS31 : 1;
			unsigned long IS30 : 1;
			unsigned long IS29 : 1;
			unsigned long IS28 : 1;
			unsigned long IS27 : 1;
			unsigned long IS26 : 1;
			unsigned long IS25 : 1;
			unsigned long IS24 : 1;
			unsigned long IS23 : 1;
			unsigned long IS22 : 1;
			unsigned long IS21 : 1;
			unsigned long IS20 : 1;
			unsigned long IS19 : 1;
			unsigned long IS18 : 1;
			unsigned long IS17 : 1;
			unsigned long IS16 : 1;
			unsigned long IS15 : 1;
			unsigned long IS14 : 1;
			unsigned long IS13 : 1;
			unsigned long IS12 : 1;
			unsigned long IS11 : 1;
			unsigned long IS10 : 1;
			unsigned long IS9 : 1;
			unsigned long IS8 : 1;
			unsigned long IS7 : 1;
			unsigned long IS6 : 1;
			unsigned long IS5 : 1;
			unsigned long IS4 : 1;
			unsigned long IS3 : 1;
			unsigned long IS2 : 1;
			unsigned long IS1 : 1;
			unsigned long IS0 : 1;
#endif
	} BIT;
	} GRPBL2;
	char           wk19[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EN0 : 1;
			unsigned long EN1 : 1;
			unsigned long EN2 : 1;
			unsigned long EN3 : 1;
			unsigned long EN4 : 1;
			unsigned long EN5 : 1;
			unsigned long EN6 : 1;
			unsigned long EN7 : 1;
			unsigned long EN8 : 1;
			unsigned long EN9 : 1;
			unsigned long EN10 : 1;
			unsigned long EN11 : 1;
			unsigned long EN12 : 1;
			unsigned long EN13 : 1;
			unsigned long EN14 : 1;
			unsigned long EN15 : 1;
			unsigned long EN16 : 1;
			unsigned long EN17 : 1;
			unsigned long EN18 : 1;
			unsigned long EN19 : 1;
			unsigned long EN20 : 1;
			unsigned long EN21 : 1;
			unsigned long EN22 : 1;
			unsigned long EN23 : 1;
			unsigned long EN24 : 1;
			unsigned long EN25 : 1;
			unsigned long EN26 : 1;
			unsigned long EN27 : 1;
			unsigned long EN28 : 1;
			unsigned long EN29 : 1;
			unsigned long EN30 : 1;
			unsigned long EN31 : 1;
#else
			unsigned long EN31 : 1;
			unsigned long EN30 : 1;
			unsigned long EN29 : 1;
			unsigned long EN28 : 1;
			unsigned long EN27 : 1;
			unsigned long EN26 : 1;
			unsigned long EN25 : 1;
			unsigned long EN24 : 1;
			unsigned long EN23 : 1;
			unsigned long EN22 : 1;
			unsigned long EN21 : 1;
			unsigned long EN20 : 1;
			unsigned long EN19 : 1;
			unsigned long EN18 : 1;
			unsigned long EN17 : 1;
			unsigned long EN16 : 1;
			unsigned long EN15 : 1;
			unsigned long EN14 : 1;
			unsigned long EN13 : 1;
			unsigned long EN12 : 1;
			unsigned long EN11 : 1;
			unsigned long EN10 : 1;
			unsigned long EN9 : 1;
			unsigned long EN8 : 1;
			unsigned long EN7 : 1;
			unsigned long EN6 : 1;
			unsigned long EN5 : 1;
			unsigned long EN4 : 1;
			unsigned long EN3 : 1;
			unsigned long EN2 : 1;
			unsigned long EN1 : 1;
			unsigned long EN0 : 1;
#endif
	} BIT;
	} GENBE0;
	char           wk20[44];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EN0 : 1;
			unsigned long EN1 : 1;
			unsigned long EN2 : 1;
			unsigned long EN3 : 1;
			unsigned long EN4 : 1;
			unsigned long EN5 : 1;
			unsigned long EN6 : 1;
			unsigned long EN7 : 1;
			unsigned long EN8 : 1;
			unsigned long EN9 : 1;
			unsigned long EN10 : 1;
			unsigned long EN11 : 1;
			unsigned long EN12 : 1;
			unsigned long EN13 : 1;
			unsigned long EN14 : 1;
			unsigned long EN15 : 1;
			unsigned long EN16 : 1;
			unsigned long EN17 : 1;
			unsigned long EN18 : 1;
			unsigned long EN19 : 1;
			unsigned long EN20 : 1;
			unsigned long EN21 : 1;
			unsigned long EN22 : 1;
			unsigned long EN23 : 1;
			unsigned long EN24 : 1;
			unsigned long EN25 : 1;
			unsigned long EN26 : 1;
			unsigned long EN27 : 1;
			unsigned long EN28 : 1;
			unsigned long EN29 : 1;
			unsigned long EN30 : 1;
			unsigned long EN31 : 1;
#else
			unsigned long EN31 : 1;
			unsigned long EN30 : 1;
			unsigned long EN29 : 1;
			unsigned long EN28 : 1;
			unsigned long EN27 : 1;
			unsigned long EN26 : 1;
			unsigned long EN25 : 1;
			unsigned long EN24 : 1;
			unsigned long EN23 : 1;
			unsigned long EN22 : 1;
			unsigned long EN21 : 1;
			unsigned long EN20 : 1;
			unsigned long EN19 : 1;
			unsigned long EN18 : 1;
			unsigned long EN17 : 1;
			unsigned long EN16 : 1;
			unsigned long EN15 : 1;
			unsigned long EN14 : 1;
			unsigned long EN13 : 1;
			unsigned long EN12 : 1;
			unsigned long EN11 : 1;
			unsigned long EN10 : 1;
			unsigned long EN9 : 1;
			unsigned long EN8 : 1;
			unsigned long EN7 : 1;
			unsigned long EN6 : 1;
			unsigned long EN5 : 1;
			unsigned long EN4 : 1;
			unsigned long EN3 : 1;
			unsigned long EN2 : 1;
			unsigned long EN1 : 1;
			unsigned long EN0 : 1;
#endif
	} BIT;
	} GENBL0;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EN0 : 1;
			unsigned long EN1 : 1;
			unsigned long EN2 : 1;
			unsigned long EN3 : 1;
			unsigned long EN4 : 1;
			unsigned long EN5 : 1;
			unsigned long EN6 : 1;
			unsigned long EN7 : 1;
			unsigned long EN8 : 1;
			unsigned long EN9 : 1;
			unsigned long EN10 : 1;
			unsigned long EN11 : 1;
			unsigned long EN12 : 1;
			unsigned long EN13 : 1;
			unsigned long EN14 : 1;
			unsigned long EN15 : 1;
			unsigned long EN16 : 1;
			unsigned long EN17 : 1;
			unsigned long EN18 : 1;
			unsigned long EN19 : 1;
			unsigned long EN20 : 1;
			unsigned long EN21 : 1;
			unsigned long EN22 : 1;
			unsigned long EN23 : 1;
			unsigned long EN24 : 1;
			unsigned long EN25 : 1;
			unsigned long EN26 : 1;
			unsigned long EN27 : 1;
			unsigned long EN28 : 1;
			unsigned long EN29 : 1;
			unsigned long EN30 : 1;
			unsigned long EN31 : 1;
#else
			unsigned long EN31 : 1;
			unsigned long EN30 : 1;
			unsigned long EN29 : 1;
			unsigned long EN28 : 1;
			unsigned long EN27 : 1;
			unsigned long EN26 : 1;
			unsigned long EN25 : 1;
			unsigned long EN24 : 1;
			unsigned long EN23 : 1;
			unsigned long EN22 : 1;
			unsigned long EN21 : 1;
			unsigned long EN20 : 1;
			unsigned long EN19 : 1;
			unsigned long EN18 : 1;
			unsigned long EN17 : 1;
			unsigned long EN16 : 1;
			unsigned long EN15 : 1;
			unsigned long EN14 : 1;
			unsigned long EN13 : 1;
			unsigned long EN12 : 1;
			unsigned long EN11 : 1;
			unsigned long EN10 : 1;
			unsigned long EN9 : 1;
			unsigned long EN8 : 1;
			unsigned long EN7 : 1;
			unsigned long EN6 : 1;
			unsigned long EN5 : 1;
			unsigned long EN4 : 1;
			unsigned long EN3 : 1;
			unsigned long EN2 : 1;
			unsigned long EN1 : 1;
			unsigned long EN0 : 1;
#endif
	} BIT;
	} GENBL1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EN0 : 1;
			unsigned long EN1 : 1;
			unsigned long EN2 : 1;
			unsigned long EN3 : 1;
			unsigned long EN4 : 1;
			unsigned long EN5 : 1;
			unsigned long EN6 : 1;
			unsigned long EN7 : 1;
			unsigned long EN8 : 1;
			unsigned long EN9 : 1;
			unsigned long EN10 : 1;
			unsigned long EN11 : 1;
			unsigned long EN12 : 1;
			unsigned long EN13 : 1;
			unsigned long EN14 : 1;
			unsigned long EN15 : 1;
			unsigned long EN16 : 1;
			unsigned long EN17 : 1;
			unsigned long EN18 : 1;
			unsigned long EN19 : 1;
			unsigned long EN20 : 1;
			unsigned long EN21 : 1;
			unsigned long EN22 : 1;
			unsigned long EN23 : 1;
			unsigned long EN24 : 1;
			unsigned long EN25 : 1;
			unsigned long EN26 : 1;
			unsigned long EN27 : 1;
			unsigned long EN28 : 1;
			unsigned long EN29 : 1;
			unsigned long EN30 : 1;
			unsigned long EN31 : 1;
#else
			unsigned long EN31 : 1;
			unsigned long EN30 : 1;
			unsigned long EN29 : 1;
			unsigned long EN28 : 1;
			unsigned long EN27 : 1;
			unsigned long EN26 : 1;
			unsigned long EN25 : 1;
			unsigned long EN24 : 1;
			unsigned long EN23 : 1;
			unsigned long EN22 : 1;
			unsigned long EN21 : 1;
			unsigned long EN20 : 1;
			unsigned long EN19 : 1;
			unsigned long EN18 : 1;
			unsigned long EN17 : 1;
			unsigned long EN16 : 1;
			unsigned long EN15 : 1;
			unsigned long EN14 : 1;
			unsigned long EN13 : 1;
			unsigned long EN12 : 1;
			unsigned long EN11 : 1;
			unsigned long EN10 : 1;
			unsigned long EN9 : 1;
			unsigned long EN8 : 1;
			unsigned long EN7 : 1;
			unsigned long EN6 : 1;
			unsigned long EN5 : 1;
			unsigned long EN4 : 1;
			unsigned long EN3 : 1;
			unsigned long EN2 : 1;
			unsigned long EN1 : 1;
			unsigned long EN0 : 1;
#endif
	} BIT;
	} GENBL2;
	char           wk21[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CLR0 : 1;
			unsigned long CLR1 : 1;
			unsigned long CLR2 : 1;
			unsigned long CLR3 : 1;
			unsigned long CLR4 : 1;
			unsigned long CLR5 : 1;
			unsigned long CLR6 : 1;
			unsigned long CLR7 : 1;
			unsigned long CLR8 : 1;
			unsigned long CLR9 : 1;
			unsigned long CLR10 : 1;
			unsigned long CLR11 : 1;
			unsigned long CLR12 : 1;
			unsigned long CLR13 : 1;
			unsigned long CLR14 : 1;
			unsigned long CLR15 : 1;
			unsigned long CLR16 : 1;
			unsigned long CLR17 : 1;
			unsigned long CLR18 : 1;
			unsigned long CLR19 : 1;
			unsigned long CLR20 : 1;
			unsigned long CLR21 : 1;
			unsigned long CLR22 : 1;
			unsigned long CLR23 : 1;
			unsigned long CLR24 : 1;
			unsigned long CLR25 : 1;
			unsigned long CLR26 : 1;
			unsigned long CLR27 : 1;
			unsigned long CLR28 : 1;
			unsigned long CLR29 : 1;
			unsigned long CLR30 : 1;
			unsigned long CLR31 : 1;
#else
			unsigned long CLR31 : 1;
			unsigned long CLR30 : 1;
			unsigned long CLR29 : 1;
			unsigned long CLR28 : 1;
			unsigned long CLR27 : 1;
			unsigned long CLR26 : 1;
			unsigned long CLR25 : 1;
			unsigned long CLR24 : 1;
			unsigned long CLR23 : 1;
			unsigned long CLR22 : 1;
			unsigned long CLR21 : 1;
			unsigned long CLR20 : 1;
			unsigned long CLR19 : 1;
			unsigned long CLR18 : 1;
			unsigned long CLR17 : 1;
			unsigned long CLR16 : 1;
			unsigned long CLR15 : 1;
			unsigned long CLR14 : 1;
			unsigned long CLR13 : 1;
			unsigned long CLR12 : 1;
			unsigned long CLR11 : 1;
			unsigned long CLR10 : 1;
			unsigned long CLR9 : 1;
			unsigned long CLR8 : 1;
			unsigned long CLR7 : 1;
			unsigned long CLR6 : 1;
			unsigned long CLR5 : 1;
			unsigned long CLR4 : 1;
			unsigned long CLR3 : 1;
			unsigned long CLR2 : 1;
			unsigned long CLR1 : 1;
			unsigned long CLR0 : 1;
#endif
	} BIT;
	} GCRBE0;
	char           wk22[124];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIBR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIBR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIBR2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIBR3;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIBR4;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIBR5;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIBR6;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIBR7;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIBR8;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIBR9;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIBRA;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIBRB;
	char           wk23[116];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBXR128;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBXR129;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBXR130;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBXR131;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBXR132;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBXR133;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBXR134;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBXR135;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBXR136;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBXR137;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBXR138;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBXR139;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBXR140;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBXR141;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBXR142;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBXR143;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR144;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR145;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR146;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR147;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR148;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR149;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR150;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR151;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR152;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR153;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR154;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR155;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR156;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR157;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR158;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR159;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR160;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR161;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR162;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR163;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR164;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR165;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR166;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR167;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR168;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR169;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR170;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR171;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR172;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR173;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR174;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR175;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR176;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR177;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR178;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR179;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR180;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR181;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR182;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR183;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR184;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR185;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR186;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR187;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR188;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR189;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR190;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR191;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR192;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR193;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR194;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR195;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR196;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR197;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR198;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR199;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR200;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR201;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR202;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR203;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR204;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR205;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR206;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLI : 8;
#else
			unsigned char SLI : 8;
#endif
	} BIT;
	} SLIBR207;
	char           wk24[96];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long IS0 : 1;
			unsigned long IS1 : 1;
			unsigned long IS2 : 1;
			unsigned long IS3 : 1;
			unsigned long IS4 : 1;
			unsigned long IS5 : 1;
			unsigned long IS6 : 1;
			unsigned long IS7 : 1;
			unsigned long IS8 : 1;
			unsigned long IS9 : 1;
			unsigned long IS10 : 1;
			unsigned long IS11 : 1;
			unsigned long IS12 : 1;
			unsigned long IS13 : 1;
			unsigned long IS14 : 1;
			unsigned long IS15 : 1;
			unsigned long IS16 : 1;
			unsigned long IS17 : 1;
			unsigned long IS18 : 1;
			unsigned long IS19 : 1;
			unsigned long IS20 : 1;
			unsigned long IS21 : 1;
			unsigned long IS22 : 1;
			unsigned long IS23 : 1;
			unsigned long IS24 : 1;
			unsigned long IS25 : 1;
			unsigned long IS26 : 1;
			unsigned long IS27 : 1;
			unsigned long IS28 : 1;
			unsigned long IS29 : 1;
			unsigned long IS30 : 1;
			unsigned long IS31 : 1;
#else
			unsigned long IS31 : 1;
			unsigned long IS30 : 1;
			unsigned long IS29 : 1;
			unsigned long IS28 : 1;
			unsigned long IS27 : 1;
			unsigned long IS26 : 1;
			unsigned long IS25 : 1;
			unsigned long IS24 : 1;
			unsigned long IS23 : 1;
			unsigned long IS22 : 1;
			unsigned long IS21 : 1;
			unsigned long IS20 : 1;
			unsigned long IS19 : 1;
			unsigned long IS18 : 1;
			unsigned long IS17 : 1;
			unsigned long IS16 : 1;
			unsigned long IS15 : 1;
			unsigned long IS14 : 1;
			unsigned long IS13 : 1;
			unsigned long IS12 : 1;
			unsigned long IS11 : 1;
			unsigned long IS10 : 1;
			unsigned long IS9 : 1;
			unsigned long IS8 : 1;
			unsigned long IS7 : 1;
			unsigned long IS6 : 1;
			unsigned long IS5 : 1;
			unsigned long IS4 : 1;
			unsigned long IS3 : 1;
			unsigned long IS2 : 1;
			unsigned long IS1 : 1;
			unsigned long IS0 : 1;
#endif
	} BIT;
	} GRPAL0;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long IS0 : 1;
			unsigned long IS1 : 1;
			unsigned long IS2 : 1;
			unsigned long IS3 : 1;
			unsigned long IS4 : 1;
			unsigned long IS5 : 1;
			unsigned long IS6 : 1;
			unsigned long IS7 : 1;
			unsigned long IS8 : 1;
			unsigned long IS9 : 1;
			unsigned long IS10 : 1;
			unsigned long IS11 : 1;
			unsigned long IS12 : 1;
			unsigned long IS13 : 1;
			unsigned long IS14 : 1;
			unsigned long IS15 : 1;
			unsigned long IS16 : 1;
			unsigned long IS17 : 1;
			unsigned long IS18 : 1;
			unsigned long IS19 : 1;
			unsigned long IS20 : 1;
			unsigned long IS21 : 1;
			unsigned long IS22 : 1;
			unsigned long IS23 : 1;
			unsigned long IS24 : 1;
			unsigned long IS25 : 1;
			unsigned long IS26 : 1;
			unsigned long IS27 : 1;
			unsigned long IS28 : 1;
			unsigned long IS29 : 1;
			unsigned long IS30 : 1;
			unsigned long IS31 : 1;
#else
			unsigned long IS31 : 1;
			unsigned long IS30 : 1;
			unsigned long IS29 : 1;
			unsigned long IS28 : 1;
			unsigned long IS27 : 1;
			unsigned long IS26 : 1;
			unsigned long IS25 : 1;
			unsigned long IS24 : 1;
			unsigned long IS23 : 1;
			unsigned long IS22 : 1;
			unsigned long IS21 : 1;
			unsigned long IS20 : 1;
			unsigned long IS19 : 1;
			unsigned long IS18 : 1;
			unsigned long IS17 : 1;
			unsigned long IS16 : 1;
			unsigned long IS15 : 1;
			unsigned long IS14 : 1;
			unsigned long IS13 : 1;
			unsigned long IS12 : 1;
			unsigned long IS11 : 1;
			unsigned long IS10 : 1;
			unsigned long IS9 : 1;
			unsigned long IS8 : 1;
			unsigned long IS7 : 1;
			unsigned long IS6 : 1;
			unsigned long IS5 : 1;
			unsigned long IS4 : 1;
			unsigned long IS3 : 1;
			unsigned long IS2 : 1;
			unsigned long IS1 : 1;
			unsigned long IS0 : 1;
#endif
	} BIT;
	} GRPAL1;
	char           wk25[56];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EN0 : 1;
			unsigned long EN1 : 1;
			unsigned long EN2 : 1;
			unsigned long EN3 : 1;
			unsigned long EN4 : 1;
			unsigned long EN5 : 1;
			unsigned long EN6 : 1;
			unsigned long EN7 : 1;
			unsigned long EN8 : 1;
			unsigned long EN9 : 1;
			unsigned long EN10 : 1;
			unsigned long EN11 : 1;
			unsigned long EN12 : 1;
			unsigned long EN13 : 1;
			unsigned long EN14 : 1;
			unsigned long EN15 : 1;
			unsigned long EN16 : 1;
			unsigned long EN17 : 1;
			unsigned long EN18 : 1;
			unsigned long EN19 : 1;
			unsigned long EN20 : 1;
			unsigned long EN21 : 1;
			unsigned long EN22 : 1;
			unsigned long EN23 : 1;
			unsigned long EN24 : 1;
			unsigned long EN25 : 1;
			unsigned long EN26 : 1;
			unsigned long EN27 : 1;
			unsigned long EN28 : 1;
			unsigned long EN29 : 1;
			unsigned long EN30 : 1;
			unsigned long EN31 : 1;
#else
			unsigned long EN31 : 1;
			unsigned long EN30 : 1;
			unsigned long EN29 : 1;
			unsigned long EN28 : 1;
			unsigned long EN27 : 1;
			unsigned long EN26 : 1;
			unsigned long EN25 : 1;
			unsigned long EN24 : 1;
			unsigned long EN23 : 1;
			unsigned long EN22 : 1;
			unsigned long EN21 : 1;
			unsigned long EN20 : 1;
			unsigned long EN19 : 1;
			unsigned long EN18 : 1;
			unsigned long EN17 : 1;
			unsigned long EN16 : 1;
			unsigned long EN15 : 1;
			unsigned long EN14 : 1;
			unsigned long EN13 : 1;
			unsigned long EN12 : 1;
			unsigned long EN11 : 1;
			unsigned long EN10 : 1;
			unsigned long EN9 : 1;
			unsigned long EN8 : 1;
			unsigned long EN7 : 1;
			unsigned long EN6 : 1;
			unsigned long EN5 : 1;
			unsigned long EN4 : 1;
			unsigned long EN3 : 1;
			unsigned long EN2 : 1;
			unsigned long EN1 : 1;
			unsigned long EN0 : 1;
#endif
	} BIT;
	} GENAL0;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long EN0 : 1;
			unsigned long EN1 : 1;
			unsigned long EN2 : 1;
			unsigned long EN3 : 1;
			unsigned long EN4 : 1;
			unsigned long EN5 : 1;
			unsigned long EN6 : 1;
			unsigned long EN7 : 1;
			unsigned long EN8 : 1;
			unsigned long EN9 : 1;
			unsigned long EN10 : 1;
			unsigned long EN11 : 1;
			unsigned long EN12 : 1;
			unsigned long EN13 : 1;
			unsigned long EN14 : 1;
			unsigned long EN15 : 1;
			unsigned long EN16 : 1;
			unsigned long EN17 : 1;
			unsigned long EN18 : 1;
			unsigned long EN19 : 1;
			unsigned long EN20 : 1;
			unsigned long EN21 : 1;
			unsigned long EN22 : 1;
			unsigned long EN23 : 1;
			unsigned long EN24 : 1;
			unsigned long EN25 : 1;
			unsigned long EN26 : 1;
			unsigned long EN27 : 1;
			unsigned long EN28 : 1;
			unsigned long EN29 : 1;
			unsigned long EN30 : 1;
			unsigned long EN31 : 1;
#else
			unsigned long EN31 : 1;
			unsigned long EN30 : 1;
			unsigned long EN29 : 1;
			unsigned long EN28 : 1;
			unsigned long EN27 : 1;
			unsigned long EN26 : 1;
			unsigned long EN25 : 1;
			unsigned long EN24 : 1;
			unsigned long EN23 : 1;
			unsigned long EN22 : 1;
			unsigned long EN21 : 1;
			unsigned long EN20 : 1;
			unsigned long EN19 : 1;
			unsigned long EN18 : 1;
			unsigned long EN17 : 1;
			unsigned long EN16 : 1;
			unsigned long EN15 : 1;
			unsigned long EN14 : 1;
			unsigned long EN13 : 1;
			unsigned long EN12 : 1;
			unsigned long EN11 : 1;
			unsigned long EN10 : 1;
			unsigned long EN9 : 1;
			unsigned long EN8 : 1;
			unsigned long EN7 : 1;
			unsigned long EN6 : 1;
			unsigned long EN5 : 1;
			unsigned long EN4 : 1;
			unsigned long EN3 : 1;
			unsigned long EN2 : 1;
			unsigned long EN1 : 1;
			unsigned long EN0 : 1;
#endif
	} BIT;
	} GENAL1;
	char           wk26[136];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIAR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIAR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIAR2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIAR3;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIAR4;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIAR5;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIAR6;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIAR7;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIAR8;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIAR9;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIARA;
	char           wk27[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PIR0 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR7 : 1;
#else
			unsigned char PIR7 : 1;
			unsigned char PIR6 : 1;
			unsigned char PIR5 : 1;
			unsigned char PIR4 : 1;
			unsigned char PIR3 : 1;
			unsigned char PIR2 : 1;
			unsigned char PIR1 : 1;
			unsigned char PIR0 : 1;
#endif
	} BIT;
	} PIARC;
	char           wk28[195];
	union {
		unsigned char BYTE;
	} SLIAR208;
	union {
		unsigned char BYTE;
	} SLIAR209;
	union {
		unsigned char BYTE;
	} SLIAR210;
	union {
		unsigned char BYTE;
	} SLIAR211;
	union {
		unsigned char BYTE;
	} SLIAR212;
	union {
		unsigned char BYTE;
	} SLIAR213;
	union {
		unsigned char BYTE;
	} SLIAR214;
	union {
		unsigned char BYTE;
	} SLIAR215;
	union {
		unsigned char BYTE;
	} SLIAR216;
	union {
		unsigned char BYTE;
	} SLIAR217;
	union {
		unsigned char BYTE;
	} SLIAR218;
	union {
		unsigned char BYTE;
	} SLIAR219;
	union {
		unsigned char BYTE;
	} SLIAR220;
	union {
		unsigned char BYTE;
	} SLIAR221;
	union {
		unsigned char BYTE;
	} SLIAR222;
	union {
		unsigned char BYTE;
	} SLIAR223;
	union {
		unsigned char BYTE;
	} SLIAR224;
	union {
		unsigned char BYTE;
	} SLIAR225;
	union {
		unsigned char BYTE;
	} SLIAR226;
	union {
		unsigned char BYTE;
	} SLIAR227;
	union {
		unsigned char BYTE;
	} SLIAR228;
	union {
		unsigned char BYTE;
	} SLIAR229;
	union {
		unsigned char BYTE;
	} SLIAR230;
	union {
		unsigned char BYTE;
	} SLIAR231;
	union {
		unsigned char BYTE;
	} SLIAR232;
	union {
		unsigned char BYTE;
	} SLIAR233;
	union {
		unsigned char BYTE;
	} SLIAR234;
	union {
		unsigned char BYTE;
	} SLIAR235;
	union {
		unsigned char BYTE;
	} SLIAR236;
	union {
		unsigned char BYTE;
	} SLIAR237;
	union {
		unsigned char BYTE;
	} SLIAR238;
	union {
		unsigned char BYTE;
	} SLIAR239;
	union {
		unsigned char BYTE;
	} SLIAR240;
	union {
		unsigned char BYTE;
	} SLIAR241;
	union {
		unsigned char BYTE;
	} SLIAR242;
	union {
		unsigned char BYTE;
	} SLIAR243;
	union {
		unsigned char BYTE;
	} SLIAR244;
	union {
		unsigned char BYTE;
	} SLIAR245;
	union {
		unsigned char BYTE;
	} SLIAR246;
	union {
		unsigned char BYTE;
	} SLIAR247;
	union {
		unsigned char BYTE;
	} SLIAR248;
	union {
		unsigned char BYTE;
	} SLIAR249;
	union {
		unsigned char BYTE;
	} SLIAR250;
	union {
		unsigned char BYTE;
	} SLIAR251;
	union {
		unsigned char BYTE;
	} SLIAR252;
	union {
		unsigned char BYTE;
	} SLIAR253;
	union {
		unsigned char BYTE;
	} SLIAR254;
	union {
		unsigned char BYTE;
	} SLIAR255;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char WPRC : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char WPRC : 1;
#endif
	} BIT;
	} SLIPRCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SELEXD0 : 1;
			unsigned char SELEXD1 : 1;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char SELEXD1 : 1;
			unsigned char SELEXD0 : 1;
#endif
	} BIT;
	} SELEXDR;
} st_icu_t;

typedef struct st_iwdt {
	unsigned char  IWDTRR;
	char           wk0[1];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short TOPS : 2;
			unsigned short  : 2;
			unsigned short CKS : 4;
			unsigned short RPES : 2;
			unsigned short  : 2;
			unsigned short RPSS : 2;
			unsigned short  : 2;
#else
			unsigned short  : 2;
			unsigned short RPSS : 2;
			unsigned short  : 2;
			unsigned short RPES : 2;
			unsigned short CKS : 4;
			unsigned short  : 2;
			unsigned short TOPS : 2;
#endif
	} BIT;
	} IWDTCR;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CNTVAL : 14;
			unsigned short UNDFF : 1;
			unsigned short REFEF : 1;
#else
			unsigned short REFEF : 1;
			unsigned short UNDFF : 1;
			unsigned short CNTVAL : 14;
#endif
	} BIT;
	} IWDTSR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 7;
			unsigned char RSTIRQS : 1;
#else
			unsigned char RSTIRQS : 1;
			unsigned char  : 7;
#endif
	} BIT;
	} IWDTRCR;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 7;
			unsigned char SLCSTP : 1;
#else
			unsigned char SLCSTP : 1;
			unsigned char  : 7;
#endif
	} BIT;
	} IWDTCSTPR;
} st_iwdt_t;

typedef struct st_mmcif {
	union {
		unsigned long LONG;
#ifdef IODEFINE_H_HISTORY
		struct {
			unsigned long :1;
			unsigned long BOOT:1;
			unsigned long CMD:6;
			unsigned long RTYP:2;
			unsigned long RBSY:1;
			unsigned long :1;
			unsigned long WDAT:1;
			unsigned long DWEN:1;
			unsigned long CMLTE:1;
			unsigned long CMD12EN:1;
			unsigned long RIDXC:2;
			unsigned long RCRC7C:2;
			unsigned long :1;
			unsigned long CRC16C:1;
			unsigned long BOOTACK:1;
			unsigned long CRCSTE:1;
			unsigned long TBIT:1;
			unsigned long OPDM:1;
			unsigned long :2;
			unsigned long SBIT:1;
			unsigned long :1;
			unsigned long DATW:2;
		} BIT;
#endif
	} CECMDSET;
	char           wk0[4];
	union {
		unsigned long LONG;
	} CEARG;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long C12ARG : 32;
#else
			unsigned long C12ARG : 32;
#endif
	} BIT;
	} CEARGCMD12;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long BREAK : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long BREAK : 1;
#endif
	} BIT;
	} CECMDCTRL;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long BLKSIZ : 16;
			unsigned long BLKCNT : 16;
#else
			unsigned long BLKCNT : 16;
			unsigned long BLKSIZ : 16;
#endif
	} BIT;
	} CEBLOCKSET;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 4;
			unsigned long SRWDTO : 4;
			unsigned long SRBSYTO : 4;
			unsigned long SRSPTO : 2;
			unsigned long  : 2;
			unsigned long CLKDIV : 4;
			unsigned long  : 4;
			unsigned long CLKEN : 1;
			unsigned long  : 6;
			unsigned long MMCBUSBSY : 1;
#else
			unsigned long MMCBUSBSY : 1;
			unsigned long  : 6;
			unsigned long CLKEN : 1;
			unsigned long  : 4;
			unsigned long CLKDIV : 4;
			unsigned long  : 2;
			unsigned long SRSPTO : 2;
			unsigned long SRBSYTO : 4;
			unsigned long SRWDTO : 4;
			unsigned long  : 4;
#endif
	} BIT;
	} CECLKCTRL;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 16;
			unsigned long ATYP : 1;
			unsigned long  : 7;
			unsigned long DMAREN : 1;
			unsigned long DMAWEN : 1;
			unsigned long DMATYP : 1;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long DMATYP : 1;
			unsigned long DMAWEN : 1;
			unsigned long DMAREN : 1;
			unsigned long  : 7;
			unsigned long ATYP : 1;
			unsigned long  : 16;
#endif
	} BIT;
	} CEBUFACC;
	unsigned long  CERESP3;
	unsigned long  CERESP2;
	unsigned long  CERESP1;
	unsigned long  CERESP0;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RSP12 : 32;
#else
			unsigned long RSP12 : 32;
#endif
	} BIT;
	} CERESPCMD12;
	unsigned long  CEDATA;
	char           wk1[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 16;
			unsigned long SBTDATTO : 4;
			unsigned long SFSTBTDATTO : 4;
			unsigned long SBTACKTO : 4;
			unsigned long SBTCLKDIV : 4;
#else
			unsigned long SBTCLKDIV : 4;
			unsigned long SBTACKTO : 4;
			unsigned long SFSTBTDATTO : 4;
			unsigned long SBTDATTO : 4;
			unsigned long  : 16;
#endif
	} BIT;
	} CEBOOT;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RSPTO : 1;
			unsigned long RBSYTO : 1;
			unsigned long RDATTO : 1;
			unsigned long WDATTO : 1;
			unsigned long CRCSTO : 1;
			unsigned long  : 3;
			unsigned long RSPERR : 1;
			unsigned long RIDXERR : 1;
			unsigned long RDATERR : 1;
			unsigned long WDATERR : 1;
			unsigned long  : 2;
			unsigned long BUFVIO : 1;
			unsigned long CMDVIO : 1;
			unsigned long CRSPE : 1;
			unsigned long RBSYE : 1;
			unsigned long  : 2;
			unsigned long BUFREN : 1;
			unsigned long BUFWEN : 1;
			unsigned long BUFRE : 1;
			unsigned long DTRANE : 1;
			unsigned long CMD12CRE : 1;
			unsigned long CMD12RBE : 1;
			unsigned long CMD12DRE : 1;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long CMD12DRE : 1;
			unsigned long CMD12RBE : 1;
			unsigned long CMD12CRE : 1;
			unsigned long DTRANE : 1;
			unsigned long BUFRE : 1;
			unsigned long BUFWEN : 1;
			unsigned long BUFREN : 1;
			unsigned long  : 2;
			unsigned long RBSYE : 1;
			unsigned long CRSPE : 1;
			unsigned long CMDVIO : 1;
			unsigned long BUFVIO : 1;
			unsigned long  : 2;
			unsigned long WDATERR : 1;
			unsigned long RDATERR : 1;
			unsigned long RIDXERR : 1;
			unsigned long RSPERR : 1;
			unsigned long  : 3;
			unsigned long CRCSTO : 1;
			unsigned long WDATTO : 1;
			unsigned long RDATTO : 1;
			unsigned long RBSYTO : 1;
			unsigned long RSPTO : 1;
#endif
	} BIT;
	} CEINT;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MRSPTO : 1;
			unsigned long MRBSYTO : 1;
			unsigned long MRDATTO : 1;
			unsigned long MWDATTO : 1;
			unsigned long MCRCSTO : 1;
			unsigned long  : 3;
			unsigned long MRSPERR : 1;
			unsigned long MRIDXERR : 1;
			unsigned long MRDATERR : 1;
			unsigned long MWDATERR : 1;
			unsigned long  : 2;
			unsigned long MBUFVIO : 1;
			unsigned long MCMDVIO : 1;
			unsigned long MCRSPE : 1;
			unsigned long MRBSYE : 1;
			unsigned long  : 2;
			unsigned long MBUFREN : 1;
			unsigned long MBUFWEN : 1;
			unsigned long MBUFRE : 1;
			unsigned long MDTRANE : 1;
			unsigned long MCMD12CRE : 1;
			unsigned long MCMD12RBE : 1;
			unsigned long MCMD12DRE : 1;
			unsigned long  : 5;
#else
			unsigned long  : 5;
			unsigned long MCMD12DRE : 1;
			unsigned long MCMD12RBE : 1;
			unsigned long MCMD12CRE : 1;
			unsigned long MDTRANE : 1;
			unsigned long MBUFRE : 1;
			unsigned long MBUFWEN : 1;
			unsigned long MBUFREN : 1;
			unsigned long  : 2;
			unsigned long MRBSYE : 1;
			unsigned long MCRSPE : 1;
			unsigned long MCMDVIO : 1;
			unsigned long MBUFVIO : 1;
			unsigned long  : 2;
			unsigned long MWDATERR : 1;
			unsigned long MRDATERR : 1;
			unsigned long MRIDXERR : 1;
			unsigned long MRSPERR : 1;
			unsigned long  : 3;
			unsigned long MCRCSTO : 1;
			unsigned long MWDATTO : 1;
			unsigned long MRDATTO : 1;
			unsigned long MRBSYTO : 1;
			unsigned long MRSPTO : 1;
#endif
	} BIT;
	} CEINTEN;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RCVBLK : 16;
			unsigned long DATSIG : 8;
			unsigned long RSPIDX : 6;
			unsigned long CMDSIG : 1;
			unsigned long CMDSEQ : 1;
#else
			unsigned long CMDSEQ : 1;
			unsigned long CMDSIG : 1;
			unsigned long RSPIDX : 6;
			unsigned long DATSIG : 8;
			unsigned long RCVBLK : 16;
#endif
	} BIT;
	} CEHOSTSTS1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 5;
			unsigned long BTDATTO : 1;
			unsigned long FSTBTDATTO : 1;
			unsigned long BTACKTO : 1;
			unsigned long STRSPTO : 1;
			unsigned long AC12RSPTO : 1;
			unsigned long RSPBSYTO : 1;
			unsigned long AC12BSYTO : 1;
			unsigned long CRCSTTO : 1;
			unsigned long DATBSYTO : 1;
			unsigned long STRDATTO : 1;
			unsigned long  : 1;
			unsigned long CRCST : 3;
			unsigned long  : 1;
			unsigned long BTACKEBE : 1;
			unsigned long BTACKPATE : 1;
			unsigned long RSPIDXE : 1;
			unsigned long AC12IDXE : 1;
			unsigned long RSPEBE : 1;
			unsigned long AC12REBE : 1;
			unsigned long RDATEBE : 1;
			unsigned long CRCSTEBE : 1;
			unsigned long RSPCRC7E : 1;
			unsigned long AC12CRCE : 1;
			unsigned long CRC16E : 1;
			unsigned long CRCSTE : 1;
#else
			unsigned long CRCSTE : 1;
			unsigned long CRC16E : 1;
			unsigned long AC12CRCE : 1;
			unsigned long RSPCRC7E : 1;
			unsigned long CRCSTEBE : 1;
			unsigned long RDATEBE : 1;
			unsigned long AC12REBE : 1;
			unsigned long RSPEBE : 1;
			unsigned long AC12IDXE : 1;
			unsigned long RSPIDXE : 1;
			unsigned long BTACKPATE : 1;
			unsigned long BTACKEBE : 1;
			unsigned long  : 1;
			unsigned long CRCST : 3;
			unsigned long  : 1;
			unsigned long STRDATTO : 1;
			unsigned long DATBSYTO : 1;
			unsigned long CRCSTTO : 1;
			unsigned long AC12BSYTO : 1;
			unsigned long RSPBSYTO : 1;
			unsigned long AC12RSPTO : 1;
			unsigned long STRSPTO : 1;
			unsigned long BTACKTO : 1;
			unsigned long FSTBTDATTO : 1;
			unsigned long BTDATTO : 1;
			unsigned long  : 5;
#endif
	} BIT;
	} CEHOSTSTS2;
	char           wk2[32];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 4;
			unsigned long MCDFALL : 1;
			unsigned long MCDRISE : 1;
			unsigned long  : 6;
			unsigned long CDFALL : 1;
			unsigned long CDRISE : 1;
			unsigned long CDSIG : 1;
			unsigned long  : 17;
#else
			unsigned long  : 17;
			unsigned long CDSIG : 1;
			unsigned long CDRISE : 1;
			unsigned long CDFALL : 1;
			unsigned long  : 6;
			unsigned long MCDRISE : 1;
			unsigned long MCDFALL : 1;
			unsigned long  : 4;
#endif
	} BIT;
	} CEDETECT;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 19;
			unsigned long CLKMAIN : 1;
			unsigned long  : 1;
			unsigned long RESNOUT : 1;
			unsigned long  : 10;
#else
			unsigned long  : 10;
			unsigned long RESNOUT : 1;
			unsigned long  : 1;
			unsigned long CLKMAIN : 1;
			unsigned long  : 19;
#endif
	} BIT;
	} CEADDMODE;
	char           wk3[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long VERSION : 16;
			unsigned long  : 15;
			unsigned long SWRST : 1;
#else
			unsigned long SWRST : 1;
			unsigned long  : 15;
			unsigned long VERSION : 16;
#endif
	} BIT;
	} CEVERSION;
} st_mmcif_t;

typedef struct st_mpc {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CS0E : 1;
			unsigned char CS1E : 1;
			unsigned char CS2E : 1;
			unsigned char CS3E : 1;
			unsigned char CS4E : 1;
			unsigned char CS5E : 1;
			unsigned char CS6E : 1;
			unsigned char CS7E : 1;
#else
			unsigned char CS7E : 1;
			unsigned char CS6E : 1;
			unsigned char CS5E : 1;
			unsigned char CS4E : 1;
			unsigned char CS3E : 1;
			unsigned char CS2E : 1;
			unsigned char CS1E : 1;
			unsigned char CS0E : 1;
#endif
	} BIT;
	} PFCSE;
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CS0S : 1;
			unsigned char  : 1;
			unsigned char CS1S : 2;
			unsigned char CS2S : 2;
			unsigned char CS3S : 2;
#else
			unsigned char CS3S : 2;
			unsigned char CS2S : 2;
			unsigned char CS1S : 2;
			unsigned char  : 1;
			unsigned char CS0S : 1;
#endif
	} BIT;
	} PFCSS0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CS4S : 2;
			unsigned char CS5S : 2;
			unsigned char CS6S : 2;
			unsigned char CS7S : 2;
#else
			unsigned char CS7S : 2;
			unsigned char CS6S : 2;
			unsigned char CS5S : 2;
			unsigned char CS4S : 2;
#endif
	} BIT;
	} PFCSS1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char A8E : 1;
			unsigned char A9E : 1;
			unsigned char A10E : 1;
			unsigned char A11E : 1;
			unsigned char A12E : 1;
			unsigned char A13E : 1;
			unsigned char A14E : 1;
			unsigned char A15E : 1;
#else
			unsigned char A15E : 1;
			unsigned char A14E : 1;
			unsigned char A13E : 1;
			unsigned char A12E : 1;
			unsigned char A11E : 1;
			unsigned char A10E : 1;
			unsigned char A9E : 1;
			unsigned char A8E : 1;
#endif
	} BIT;
	} PFAOE0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char A16E : 1;
			unsigned char A17E : 1;
			unsigned char A18E : 1;
			unsigned char A19E : 1;
			unsigned char A20E : 1;
			unsigned char A21E : 1;
			unsigned char A22E : 1;
			unsigned char A23E : 1;
#else
			unsigned char A23E : 1;
			unsigned char A22E : 1;
			unsigned char A21E : 1;
			unsigned char A20E : 1;
			unsigned char A19E : 1;
			unsigned char A18E : 1;
			unsigned char A17E : 1;
			unsigned char A16E : 1;
#endif
	} BIT;
	} PFAOE1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ADRLE : 1;
			unsigned char ADRHMS : 1;
			unsigned char ADRHMS2 : 1;
			unsigned char BCLKO : 1;
			unsigned char DHE : 1;
			unsigned char DH32E : 1;
			unsigned char WR1BC1E : 1;
			unsigned char WR32BC32E : 1;
#else
			unsigned char WR32BC32E : 1;
			unsigned char WR1BC1E : 1;
			unsigned char DH32E : 1;
			unsigned char DHE : 1;
			unsigned char BCLKO : 1;
			unsigned char ADRHMS2 : 1;
			unsigned char ADRHMS : 1;
			unsigned char ADRLE : 1;
#endif
	} BIT;
	} PFBCR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char WAITS : 2;
			unsigned char ALEOE : 1;
			unsigned char ALES : 1;
			unsigned char MDSDE : 1;
			unsigned char  : 1;
			unsigned char DQM1E : 1;
			unsigned char SDCLKE : 1;
#else
			unsigned char SDCLKE : 1;
			unsigned char DQM1E : 1;
			unsigned char  : 1;
			unsigned char MDSDE : 1;
			unsigned char ALES : 1;
			unsigned char ALEOE : 1;
			unsigned char WAITS : 2;
#endif
	} BIT;
	} PFBCR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char D0S : 2;
			unsigned char D1S : 2;
			unsigned char D2S : 2;
			unsigned char D3S : 2;
#else
			unsigned char D3S : 2;
			unsigned char D2S : 2;
			unsigned char D1S : 2;
			unsigned char D0S : 2;
#endif
	} BIT;
	} PFBCR2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DLHS : 1;
			unsigned char  : 5;
			unsigned char SDCLKDRV : 1;
			unsigned char WAITS2 : 1;
#else
			unsigned char WAITS2 : 1;
			unsigned char SDCLKDRV : 1;
			unsigned char  : 5;
			unsigned char DLHS : 1;
#endif
	} BIT;
	} PFBCR3;
	char           wk1[4];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 4;
			unsigned char PHYMODE0 : 1;
			unsigned char PHYMODE1 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PHYMODE1 : 1;
			unsigned char PHYMODE0 : 1;
			unsigned char  : 4;
#endif
	} BIT;
	} PFENET;
	char           wk2[16];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 6;
			unsigned char PFSWE : 1;
			unsigned char B0WI : 1;
#else
			unsigned char B0WI : 1;
			unsigned char PFSWE : 1;
			unsigned char  : 6;
#endif
	} BIT;
	} PWPR;
	char           wk3[32];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P00PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P01PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P02PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char  : 6;
#endif
	} BIT;
	} P03PFS;
	char           wk4[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char  : 6;
#endif
	} BIT;
	} P05PFS;
	char           wk5[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P07PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P10PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P11PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P12PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P13PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P14PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P15PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P16PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P17PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P20PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P21PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P22PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P23PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P24PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P25PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P26PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P27PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P30PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P31PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P32PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P33PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P34PFS;
	char           wk6[3];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char  : 6;
#endif
	} BIT;
	} P40PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char  : 6;
#endif
	} BIT;
	} P41PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char  : 6;
#endif
	} BIT;
	} P42PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char  : 6;
#endif
	} BIT;
	} P43PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char  : 6;
#endif
	} BIT;
	} P44PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char  : 6;
#endif
	} BIT;
	} P45PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char  : 6;
#endif
	} BIT;
	} P46PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char  : 6;
#endif
	} BIT;
	} P47PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P50PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P51PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P52PFS;
	char           wk7[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P54PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P55PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P56PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P57PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P60PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P61PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P62PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P63PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P64PFS;
	char           wk8[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P66PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P67PFS;
	char           wk9[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P71PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P72PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P73PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P74PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P75PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P76PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P77PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P80PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P81PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P82PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P83PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P84PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P85PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P86PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P87PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char  : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P90PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char  : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P91PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char  : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P92PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char  : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P93PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P94PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P95PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P96PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} P97PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PA0PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PA1PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PA2PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PA3PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PA4PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PA5PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PA6PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PA7PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PB0PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PB1PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PB2PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PB3PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PB4PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PB5PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PB6PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PB7PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PC0PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PC1PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PC2PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PC3PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PC4PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PC5PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PC6PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PC7PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PD0PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PD1PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PD2PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PD3PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PD4PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PD5PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PD6PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PD7PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char  : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PE0PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char  : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PE1PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PE2PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char  : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PE3PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char  : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PE4PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PE5PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PE6PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char ISEL : 1;
			unsigned char ASEL : 1;
#else
			unsigned char ASEL : 1;
			unsigned char ISEL : 1;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PE7PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PF0PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PF1PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PF2PFS;
	char           wk10[2];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 6;
			unsigned char ISEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ISEL : 1;
			unsigned char  : 6;
#endif
	} BIT;
	} PF5PFS;
	char           wk11[2];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PG0PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PG1PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PG2PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PG3PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PG4PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PG5PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PG6PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PG7PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PH0PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PH1PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PH2PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PH3PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PH4PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PH5PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PH6PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PH7PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PJ0PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PJ1PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PJ2PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PJ3PFS;
	char           wk12[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PJ5PFS;
	char           wk13[2];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PK0PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PK1PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PK2PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PK3PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PK4PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PK5PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PK6PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PK7PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PL0PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PL1PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PL2PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PL3PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PL4PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PL5PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PL6PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PL7PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PM0PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PM1PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PM2PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PM3PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PM4PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PM5PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PM6PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PM7PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PN0PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PN1PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PN2PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PN3PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PN4PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PN5PFS;
	char           wk14[2];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PQ0PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PQ1PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PQ2PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PQ3PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PQ4PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PQ5PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PQ6PFS;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PSEL : 6;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PSEL : 6;
#endif
	} BIT;
	} PQ7PFS;
} st_mpc_t;

typedef struct st_mpu {
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 4;
			unsigned long RSPN : 28;
#else
			unsigned long RSPN : 28;
			unsigned long  : 4;
#endif
	} BIT;
	} RSPAGE0;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long V : 1;
			unsigned long UAC : 3;
			unsigned long REPN : 28;
#else
			unsigned long REPN : 28;
			unsigned long UAC : 3;
			unsigned long V : 1;
#endif
	} BIT;
	} REPAGE0;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 4;
			unsigned long RSPN : 28;
#else
			unsigned long RSPN : 28;
			unsigned long  : 4;
#endif
	} BIT;
	} RSPAGE1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long V : 1;
			unsigned long UAC : 3;
			unsigned long REPN : 28;
#else
			unsigned long REPN : 28;
			unsigned long UAC : 3;
			unsigned long V : 1;
#endif
	} BIT;
	} REPAGE1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 4;
			unsigned long RSPN : 28;
#else
			unsigned long RSPN : 28;
			unsigned long  : 4;
#endif
	} BIT;
	} RSPAGE2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long V : 1;
			unsigned long UAC : 3;
			unsigned long REPN : 28;
#else
			unsigned long REPN : 28;
			unsigned long UAC : 3;
			unsigned long V : 1;
#endif
	} BIT;
	} REPAGE2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 4;
			unsigned long RSPN : 28;
#else
			unsigned long RSPN : 28;
			unsigned long  : 4;
#endif
	} BIT;
	} RSPAGE3;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long V : 1;
			unsigned long UAC : 3;
			unsigned long REPN : 28;
#else
			unsigned long REPN : 28;
			unsigned long UAC : 3;
			unsigned long V : 1;
#endif
	} BIT;
	} REPAGE3;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 4;
			unsigned long RSPN : 28;
#else
			unsigned long RSPN : 28;
			unsigned long  : 4;
#endif
	} BIT;
	} RSPAGE4;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long V : 1;
			unsigned long UAC : 3;
			unsigned long REPN : 28;
#else
			unsigned long REPN : 28;
			unsigned long UAC : 3;
			unsigned long V : 1;
#endif
	} BIT;
	} REPAGE4;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 4;
			unsigned long RSPN : 28;
#else
			unsigned long RSPN : 28;
			unsigned long  : 4;
#endif
	} BIT;
	} RSPAGE5;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long V : 1;
			unsigned long UAC : 3;
			unsigned long REPN : 28;
#else
			unsigned long REPN : 28;
			unsigned long UAC : 3;
			unsigned long V : 1;
#endif
	} BIT;
	} REPAGE5;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 4;
			unsigned long RSPN : 28;
#else
			unsigned long RSPN : 28;
			unsigned long  : 4;
#endif
	} BIT;
	} RSPAGE6;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long V : 1;
			unsigned long UAC : 3;
			unsigned long REPN : 28;
#else
			unsigned long REPN : 28;
			unsigned long UAC : 3;
			unsigned long V : 1;
#endif
	} BIT;
	} REPAGE6;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 4;
			unsigned long RSPN : 28;
#else
			unsigned long RSPN : 28;
			unsigned long  : 4;
#endif
	} BIT;
	} RSPAGE7;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long V : 1;
			unsigned long UAC : 3;
			unsigned long REPN : 28;
#else
			unsigned long REPN : 28;
			unsigned long UAC : 3;
			unsigned long V : 1;
#endif
	} BIT;
	} REPAGE7;
	char           wk0[192];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MPEN : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long MPEN : 1;
#endif
	} BIT;
	} MPEN;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 1;
			unsigned long UBAC : 3;
			unsigned long  : 28;
#else
			unsigned long  : 28;
			unsigned long UBAC : 3;
			unsigned long  : 1;
#endif
	} BIT;
	} MPBAC;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CLR : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long CLR : 1;
#endif
	} BIT;
	} MPECLR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long IMPER : 1;
			unsigned long DMPER : 1;
			unsigned long DRW : 1;
			unsigned long  : 29;
#else
			unsigned long  : 29;
			unsigned long DRW : 1;
			unsigned long DMPER : 1;
			unsigned long IMPER : 1;
#endif
	} BIT;
	} MPESTS;
	char           wk1[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long DEA : 32;
#else
			unsigned long DEA : 32;
#endif
	} BIT;
	} MPDEA;
	char           wk2[8];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long SA : 32;
#else
			unsigned long SA : 32;
#endif
	} BIT;
	} MPSA;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short S : 1;
			unsigned short  : 15;
#else
			unsigned short  : 15;
			unsigned short S : 1;
#endif
	} BIT;
	} MPOPS;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short INV : 1;
			unsigned short  : 15;
#else
			unsigned short  : 15;
			unsigned short INV : 1;
#endif
	} BIT;
	} MPOPI;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 1;
			unsigned long UHACI : 3;
			unsigned long  : 12;
			unsigned long HITI : 8;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long HITI : 8;
			unsigned long  : 12;
			unsigned long UHACI : 3;
			unsigned long  : 1;
#endif
	} BIT;
	} MHITI;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 1;
			unsigned long UHACD : 3;
			unsigned long  : 12;
			unsigned long HITD : 8;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long HITD : 8;
			unsigned long  : 12;
			unsigned long UHACD : 3;
			unsigned long  : 1;
#endif
	} BIT;
	} MHITD;
} st_mpu_t;

typedef struct st_mtu {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char OE3B : 1;
			unsigned char OE4A : 1;
			unsigned char OE4B : 1;
			unsigned char OE3D : 1;
			unsigned char OE4C : 1;
			unsigned char OE4D : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char OE4D : 1;
			unsigned char OE4C : 1;
			unsigned char OE3D : 1;
			unsigned char OE4B : 1;
			unsigned char OE4A : 1;
			unsigned char OE3B : 1;
#endif
	} BIT;
	} TOERA;
	char           wk0[2];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char UF : 1;
			unsigned char VF : 1;
			unsigned char WF : 1;
			unsigned char FB : 1;
			unsigned char P : 1;
			unsigned char N : 1;
			unsigned char BDC : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char BDC : 1;
			unsigned char N : 1;
			unsigned char P : 1;
			unsigned char FB : 1;
			unsigned char WF : 1;
			unsigned char VF : 1;
			unsigned char UF : 1;
#endif
	} BIT;
	} TGCRA;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char OLSP : 1;
			unsigned char OLSN : 1;
			unsigned char TOCS : 1;
			unsigned char TOCL : 1;
			unsigned char  : 2;
			unsigned char PSYE : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char PSYE : 1;
			unsigned char  : 2;
			unsigned char TOCL : 1;
			unsigned char TOCS : 1;
			unsigned char OLSN : 1;
			unsigned char OLSP : 1;
#endif
	} BIT;
	} TOCR1A;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char OLS1P : 1;
			unsigned char OLS1N : 1;
			unsigned char OLS2P : 1;
			unsigned char OLS2N : 1;
			unsigned char OLS3P : 1;
			unsigned char OLS3N : 1;
			unsigned char BF : 2;
#else
			unsigned char BF : 2;
			unsigned char OLS3N : 1;
			unsigned char OLS3P : 1;
			unsigned char OLS2N : 1;
			unsigned char OLS2P : 1;
			unsigned char OLS1N : 1;
			unsigned char OLS1P : 1;
#endif
	} BIT;
	} TOCR2A;
	char           wk1[4];
	unsigned short TCDRA;
	unsigned short TDDRA;
	char           wk2[8];
	unsigned short TCNTSA;
	unsigned short TCBRA;
	char           wk3[12];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char T4VCOR : 3;
			unsigned char T4VEN : 1;
			unsigned char T3ACOR : 3;
			unsigned char T3AEN : 1;
#else
			unsigned char T3AEN : 1;
			unsigned char T3ACOR : 3;
			unsigned char T4VEN : 1;
			unsigned char T4VCOR : 3;
#endif
	} BIT;
	} TITCR1A;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char T4VCNT : 3;
			unsigned char  : 1;
			unsigned char T3ACNT : 3;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char T3ACNT : 3;
			unsigned char  : 1;
			unsigned char T4VCNT : 3;
#endif
	} BIT;
	} TITCNT1A;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BTE : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char BTE : 2;
#endif
	} BIT;
	} TBTERA;
	char           wk4[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TDER : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char TDER : 1;
#endif
	} BIT;
	} TDERA;
	char           wk5[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char OLS1P : 1;
			unsigned char OLS1N : 1;
			unsigned char OLS2P : 1;
			unsigned char OLS2N : 1;
			unsigned char OLS3P : 1;
			unsigned char OLS3N : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char OLS3N : 1;
			unsigned char OLS3P : 1;
			unsigned char OLS2N : 1;
			unsigned char OLS2P : 1;
			unsigned char OLS1N : 1;
			unsigned char OLS1P : 1;
#endif
	} BIT;
	} TOLBRA;
	char           wk6[3];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TITM : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char TITM : 1;
#endif
	} BIT;
	} TITMRA;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TRG4COR : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char TRG4COR : 3;
#endif
	} BIT;
	} TITCR2A;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TRG4CNT : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char TRG4CNT : 3;
#endif
	} BIT;
	} TITCNT2A;
	char           wk7[35];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char WRE : 1;
			unsigned char SCC : 1;
			unsigned char  : 5;
			unsigned char CCE : 1;
#else
			unsigned char CCE : 1;
			unsigned char  : 5;
			unsigned char SCC : 1;
			unsigned char WRE : 1;
#endif
	} BIT;
	} TWCRA;
	char           wk8[15];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DRS : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char DRS : 1;
#endif
	} BIT;
	} TMDR2A;
	char           wk9[15];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CST0 : 1;
			unsigned char CST1 : 1;
			unsigned char CST2 : 1;
			unsigned char CST8 : 1;
			unsigned char  : 2;
			unsigned char CST3 : 1;
			unsigned char CST4 : 1;
#else
			unsigned char CST4 : 1;
			unsigned char CST3 : 1;
			unsigned char  : 2;
			unsigned char CST8 : 1;
			unsigned char CST2 : 1;
			unsigned char CST1 : 1;
			unsigned char CST0 : 1;
#endif
	} BIT;
	} TSTRA;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SYNC0 : 1;
			unsigned char SYNC1 : 1;
			unsigned char SYNC2 : 1;
			unsigned char  : 3;
			unsigned char SYNC3 : 1;
			unsigned char SYNC4 : 1;
#else
			unsigned char SYNC4 : 1;
			unsigned char SYNC3 : 1;
			unsigned char  : 3;
			unsigned char SYNC2 : 1;
			unsigned char SYNC1 : 1;
			unsigned char SYNC0 : 1;
#endif
	} BIT;
	} TSYRA;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SCH7 : 1;
			unsigned char SCH6 : 1;
			unsigned char  : 1;
			unsigned char SCH4 : 1;
			unsigned char SCH3 : 1;
			unsigned char SCH2 : 1;
			unsigned char SCH1 : 1;
			unsigned char SCH0 : 1;
#else
			unsigned char SCH0 : 1;
			unsigned char SCH1 : 1;
			unsigned char SCH2 : 1;
			unsigned char SCH3 : 1;
			unsigned char SCH4 : 1;
			unsigned char  : 1;
			unsigned char SCH6 : 1;
			unsigned char SCH7 : 1;
#endif
	} BIT;
	} TCSYSTR;
	char           wk10[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char RWE : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char RWE : 1;
#endif
	} BIT;
	} TRWERA;
	char           wk11[1925];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char OE6B : 1;
			unsigned char OE7A : 1;
			unsigned char OE7B : 1;
			unsigned char OE6D : 1;
			unsigned char OE7C : 1;
			unsigned char OE7D : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char OE7D : 1;
			unsigned char OE7C : 1;
			unsigned char OE6D : 1;
			unsigned char OE7B : 1;
			unsigned char OE7A : 1;
			unsigned char OE6B : 1;
#endif
	} BIT;
	} TOERB;
	char           wk12[3];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char OLSP : 1;
			unsigned char OLSN : 1;
			unsigned char TOCS : 1;
			unsigned char TOCL : 1;
			unsigned char  : 2;
			unsigned char PSYE : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char PSYE : 1;
			unsigned char  : 2;
			unsigned char TOCL : 1;
			unsigned char TOCS : 1;
			unsigned char OLSN : 1;
			unsigned char OLSP : 1;
#endif
	} BIT;
	} TOCR1B;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char OLS1P : 1;
			unsigned char OLS1N : 1;
			unsigned char OLS2P : 1;
			unsigned char OLS2N : 1;
			unsigned char OLS3P : 1;
			unsigned char OLS3N : 1;
			unsigned char BF : 2;
#else
			unsigned char BF : 2;
			unsigned char OLS3N : 1;
			unsigned char OLS3P : 1;
			unsigned char OLS2N : 1;
			unsigned char OLS2P : 1;
			unsigned char OLS1N : 1;
			unsigned char OLS1P : 1;
#endif
	} BIT;
	} TOCR2B;
	char           wk13[4];
	unsigned short TCDRB;
	unsigned short TDDRB;
	char           wk14[8];
	unsigned short TCNTSB;
	unsigned short TCBRB;
	char           wk15[12];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char T7VCOR : 3;
			unsigned char T7VEN : 1;
			unsigned char T6ACOR : 3;
			unsigned char T6AEN : 1;
#else
			unsigned char T6AEN : 1;
			unsigned char T6ACOR : 3;
			unsigned char T7VEN : 1;
			unsigned char T7VCOR : 3;
#endif
	} BIT;
	} TITCR1B;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char T7VCNT : 3;
			unsigned char  : 1;
			unsigned char T6ACNT : 3;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char T6ACNT : 3;
			unsigned char  : 1;
			unsigned char T7VCNT : 3;
#endif
	} BIT;
	} TITCNT1B;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BTE : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char BTE : 2;
#endif
	} BIT;
	} TBTERB;
	char           wk16[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TDER : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char TDER : 1;
#endif
	} BIT;
	} TDERB;
	char           wk17[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char OLS1P : 1;
			unsigned char OLS1N : 1;
			unsigned char OLS2P : 1;
			unsigned char OLS2N : 1;
			unsigned char OLS3P : 1;
			unsigned char OLS3N : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char OLS3N : 1;
			unsigned char OLS3P : 1;
			unsigned char OLS2N : 1;
			unsigned char OLS2P : 1;
			unsigned char OLS1N : 1;
			unsigned char OLS1P : 1;
#endif
	} BIT;
	} TOLBRB;
	char           wk18[3];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TITM : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char TITM : 1;
#endif
	} BIT;
	} TITMRB;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TRG7COR : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char TRG7COR : 3;
#endif
	} BIT;
	} TITCR2B;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TRG7CNT : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char TRG7CNT : 3;
#endif
	} BIT;
	} TITCNT2B;
	char           wk19[35];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char WRE : 1;
			unsigned char SCC : 1;
			unsigned char  : 5;
			unsigned char CCE : 1;
#else
			unsigned char CCE : 1;
			unsigned char  : 5;
			unsigned char SCC : 1;
			unsigned char WRE : 1;
#endif
	} BIT;
	} TWCRB;
	char           wk20[15];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DRS : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char DRS : 1;
#endif
	} BIT;
	} TMDR2B;
	char           wk21[15];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 6;
			unsigned char CST6 : 1;
			unsigned char CST7 : 1;
#else
			unsigned char CST7 : 1;
			unsigned char CST6 : 1;
			unsigned char  : 6;
#endif
	} BIT;
	} TSTRB;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 6;
			unsigned char SYNC6 : 1;
			unsigned char SYNC7 : 1;
#else
			unsigned char SYNC7 : 1;
			unsigned char SYNC6 : 1;
			unsigned char  : 6;
#endif
	} BIT;
	} TSYRB;
	char           wk22[2];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char RWE : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char RWE : 1;
#endif
	} BIT;
	} TRWERB;
} st_mtu_t;

typedef struct st_mtu0 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFAEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFDEN : 1;
			unsigned char NFCS : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char NFCS : 2;
			unsigned char NFDEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFAEN : 1;
#endif
	} BIT;
	} NFCR0;
	char           wk0[8];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFAEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFDEN : 1;
			unsigned char NFCS : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char NFCS : 2;
			unsigned char NFDEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFAEN : 1;
#endif
	} BIT;
	} NFCRC;
	char           wk1[102];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC : 3;
			unsigned char CKEG : 2;
			unsigned char CCLR : 3;
#else
			unsigned char CCLR : 3;
			unsigned char CKEG : 2;
			unsigned char TPSC : 3;
#endif
	} BIT;
	} TCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MD : 4;
			unsigned char BFA : 1;
			unsigned char BFB : 1;
			unsigned char BFE : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char BFE : 1;
			unsigned char BFB : 1;
			unsigned char BFA : 1;
			unsigned char MD : 4;
#endif
	} BIT;
	} TMDR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOA : 4;
			unsigned char IOB : 4;
#else
			unsigned char IOB : 4;
			unsigned char IOA : 4;
#endif
	} BIT;
	} TIORH;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOC : 4;
			unsigned char IOD : 4;
#else
			unsigned char IOD : 4;
			unsigned char IOC : 4;
#endif
	} BIT;
	} TIORL;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGIEA : 1;
			unsigned char TGIEB : 1;
			unsigned char TGIEC : 1;
			unsigned char TGIED : 1;
			unsigned char TCIEV : 1;
			unsigned char  : 2;
			unsigned char TTGE : 1;
#else
			unsigned char TTGE : 1;
			unsigned char  : 2;
			unsigned char TCIEV : 1;
			unsigned char TGIED : 1;
			unsigned char TGIEC : 1;
			unsigned char TGIEB : 1;
			unsigned char TGIEA : 1;
#endif
	} BIT;
	} TIER;
	char           wk2[1];
	unsigned short TCNT;
	unsigned short TGRA;
	unsigned short TGRB;
	unsigned short TGRC;
	unsigned short TGRD;
	char           wk3[16];
	unsigned short TGRE;
	unsigned short TGRF;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGIEE : 1;
			unsigned char TGIEF : 1;
			unsigned char  : 5;
			unsigned char TTGE2 : 1;
#else
			unsigned char TTGE2 : 1;
			unsigned char  : 5;
			unsigned char TGIEF : 1;
			unsigned char TGIEE : 1;
#endif
	} BIT;
	} TIER2;
	char           wk4[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TTSA : 1;
			unsigned char TTSB : 1;
			unsigned char TTSE : 1;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char TTSE : 1;
			unsigned char TTSB : 1;
			unsigned char TTSA : 1;
#endif
	} BIT;
	} TBTM;
	char           wk5[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC2 : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char TPSC2 : 3;
#endif
	} BIT;
	} TCR2;
} st_mtu0_t;

typedef struct st_mtu1 {
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFAEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFDEN : 1;
			unsigned char NFCS : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char NFCS : 2;
			unsigned char NFDEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFAEN : 1;
#endif
	} BIT;
	} NFCR1;
	char           wk1[238];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC : 3;
			unsigned char CKEG : 2;
			unsigned char CCLR : 2;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char CCLR : 2;
			unsigned char CKEG : 2;
			unsigned char TPSC : 3;
#endif
	} BIT;
	} TCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MD : 4;
			unsigned char  : 4;
#else
			unsigned char  : 4;
			unsigned char MD : 4;
#endif
	} BIT;
	} TMDR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOA : 4;
			unsigned char IOB : 4;
#else
			unsigned char IOB : 4;
			unsigned char IOA : 4;
#endif
	} BIT;
	} TIOR;
	char           wk2[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGIEA : 1;
			unsigned char TGIEB : 1;
			unsigned char  : 2;
			unsigned char TCIEV : 1;
			unsigned char TCIEU : 1;
			unsigned char  : 1;
			unsigned char TTGE : 1;
#else
			unsigned char TTGE : 1;
			unsigned char  : 1;
			unsigned char TCIEU : 1;
			unsigned char TCIEV : 1;
			unsigned char  : 2;
			unsigned char TGIEB : 1;
			unsigned char TGIEA : 1;
#endif
	} BIT;
	} TIER;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 7;
			unsigned char TCFD : 1;
#else
			unsigned char TCFD : 1;
			unsigned char  : 7;
#endif
	} BIT;
	} TSR;
	unsigned short TCNT;
	unsigned short TGRA;
	unsigned short TGRB;
	char           wk3[4];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char I1AE : 1;
			unsigned char I1BE : 1;
			unsigned char I2AE : 1;
			unsigned char I2BE : 1;
			unsigned char  : 4;
#else
			unsigned char  : 4;
			unsigned char I2BE : 1;
			unsigned char I2AE : 1;
			unsigned char I1BE : 1;
			unsigned char I1AE : 1;
#endif
	} BIT;
	} TICCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char LWA : 1;
			unsigned char PHCKSEL : 1;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char PHCKSEL : 1;
			unsigned char LWA : 1;
#endif
	} BIT;
	} TMDR3;
	char           wk4[2];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC2 : 3;
			unsigned char PCB : 2;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char PCB : 2;
			unsigned char TPSC2 : 3;
#endif
	} BIT;
	} TCR2;
	char           wk5[11];
	unsigned long  TCNTLW;
	unsigned long  TGRALW;
	unsigned long  TGRBLW;
} st_mtu1_t;

typedef struct st_mtu2 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFAEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFDEN : 1;
			unsigned char NFCS : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char NFCS : 2;
			unsigned char NFDEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFAEN : 1;
#endif
	} BIT;
	} NFCR2;
	char           wk0[365];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC : 3;
			unsigned char CKEG : 2;
			unsigned char CCLR : 2;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char CCLR : 2;
			unsigned char CKEG : 2;
			unsigned char TPSC : 3;
#endif
	} BIT;
	} TCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MD : 4;
			unsigned char  : 4;
#else
			unsigned char  : 4;
			unsigned char MD : 4;
#endif
	} BIT;
	} TMDR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOA : 4;
			unsigned char IOB : 4;
#else
			unsigned char IOB : 4;
			unsigned char IOA : 4;
#endif
	} BIT;
	} TIOR;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGIEA : 1;
			unsigned char TGIEB : 1;
			unsigned char  : 2;
			unsigned char TCIEV : 1;
			unsigned char TCIEU : 1;
			unsigned char  : 1;
			unsigned char TTGE : 1;
#else
			unsigned char TTGE : 1;
			unsigned char  : 1;
			unsigned char TCIEU : 1;
			unsigned char TCIEV : 1;
			unsigned char  : 2;
			unsigned char TGIEB : 1;
			unsigned char TGIEA : 1;
#endif
	} BIT;
	} TIER;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 7;
			unsigned char TCFD : 1;
#else
			unsigned char TCFD : 1;
			unsigned char  : 7;
#endif
	} BIT;
	} TSR;
	unsigned short TCNT;
	unsigned short TGRA;
	unsigned short TGRB;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC2 : 3;
			unsigned char PCB : 2;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char PCB : 2;
			unsigned char TPSC2 : 3;
#endif
	} BIT;
	} TCR2;
} st_mtu2_t;

typedef struct st_mtu3 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC : 3;
			unsigned char CKEG : 2;
			unsigned char CCLR : 3;
#else
			unsigned char CCLR : 3;
			unsigned char CKEG : 2;
			unsigned char TPSC : 3;
#endif
	} BIT;
	} TCR;
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MD : 4;
			unsigned char BFA : 1;
			unsigned char BFB : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char BFB : 1;
			unsigned char BFA : 1;
			unsigned char MD : 4;
#endif
	} BIT;
	} TMDR1;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOA : 4;
			unsigned char IOB : 4;
#else
			unsigned char IOB : 4;
			unsigned char IOA : 4;
#endif
	} BIT;
	} TIORH;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOC : 4;
			unsigned char IOD : 4;
#else
			unsigned char IOD : 4;
			unsigned char IOC : 4;
#endif
	} BIT;
	} TIORL;
	char           wk2[2];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGIEA : 1;
			unsigned char TGIEB : 1;
			unsigned char TGIEC : 1;
			unsigned char TGIED : 1;
			unsigned char TCIEV : 1;
			unsigned char  : 2;
			unsigned char TTGE : 1;
#else
			unsigned char TTGE : 1;
			unsigned char  : 2;
			unsigned char TCIEV : 1;
			unsigned char TGIED : 1;
			unsigned char TGIEC : 1;
			unsigned char TGIEB : 1;
			unsigned char TGIEA : 1;
#endif
	} BIT;
	} TIER;
	char           wk3[7];
	unsigned short TCNT;
	char           wk4[6];
	unsigned short TGRA;
	unsigned short TGRB;
	char           wk5[8];
	unsigned short TGRC;
	unsigned short TGRD;
	char           wk6[4];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 7;
			unsigned char TCFD : 1;
#else
			unsigned char TCFD : 1;
			unsigned char  : 7;
#endif
	} BIT;
	} TSR;
	char           wk7[11];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TTSA : 1;
			unsigned char TTSB : 1;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char TTSB : 1;
			unsigned char TTSA : 1;
#endif
	} BIT;
	} TBTM;
	char           wk8[19];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC2 : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char TPSC2 : 3;
#endif
	} BIT;
	} TCR2;
	char           wk9[37];
	unsigned short TGRE;
	char           wk10[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFAEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFDEN : 1;
			unsigned char NFCS : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char NFCS : 2;
			unsigned char NFDEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFAEN : 1;
#endif
	} BIT;
	} NFCR3;
} st_mtu3_t;

typedef struct st_mtu4 {
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC : 3;
			unsigned char CKEG : 2;
			unsigned char CCLR : 3;
#else
			unsigned char CCLR : 3;
			unsigned char CKEG : 2;
			unsigned char TPSC : 3;
#endif
	} BIT;
	} TCR;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MD : 4;
			unsigned char BFA : 1;
			unsigned char BFB : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char BFB : 1;
			unsigned char BFA : 1;
			unsigned char MD : 4;
#endif
	} BIT;
	} TMDR1;
	char           wk2[2];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOA : 4;
			unsigned char IOB : 4;
#else
			unsigned char IOB : 4;
			unsigned char IOA : 4;
#endif
	} BIT;
	} TIORH;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOC : 4;
			unsigned char IOD : 4;
#else
			unsigned char IOD : 4;
			unsigned char IOC : 4;
#endif
	} BIT;
	} TIORL;
	char           wk3[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGIEA : 1;
			unsigned char TGIEB : 1;
			unsigned char TGIEC : 1;
			unsigned char TGIED : 1;
			unsigned char TCIEV : 1;
			unsigned char  : 1;
			unsigned char TTGE2 : 1;
			unsigned char TTGE : 1;
#else
			unsigned char TTGE : 1;
			unsigned char TTGE2 : 1;
			unsigned char  : 1;
			unsigned char TCIEV : 1;
			unsigned char TGIED : 1;
			unsigned char TGIEC : 1;
			unsigned char TGIEB : 1;
			unsigned char TGIEA : 1;
#endif
	} BIT;
	} TIER;
	char           wk4[8];
	unsigned short TCNT;
	char           wk5[8];
	unsigned short TGRA;
	unsigned short TGRB;
	char           wk6[8];
	unsigned short TGRC;
	unsigned short TGRD;
	char           wk7[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 7;
			unsigned char TCFD : 1;
#else
			unsigned char TCFD : 1;
			unsigned char  : 7;
#endif
	} BIT;
	} TSR;
	char           wk8[11];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TTSA : 1;
			unsigned char TTSB : 1;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char TTSB : 1;
			unsigned char TTSA : 1;
#endif
	} BIT;
	} TBTM;
	char           wk9[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ITB4VE : 1;
			unsigned short ITB3AE : 1;
			unsigned short ITA4VE : 1;
			unsigned short ITA3AE : 1;
			unsigned short DT4BE : 1;
			unsigned short UT4BE : 1;
			unsigned short DT4AE : 1;
			unsigned short UT4AE : 1;
			unsigned short  : 6;
			unsigned short BF : 2;
#else
			unsigned short BF : 2;
			unsigned short  : 6;
			unsigned short UT4AE : 1;
			unsigned short DT4AE : 1;
			unsigned short UT4BE : 1;
			unsigned short DT4BE : 1;
			unsigned short ITA3AE : 1;
			unsigned short ITA4VE : 1;
			unsigned short ITB3AE : 1;
			unsigned short ITB4VE : 1;
#endif
	} BIT;
	} TADCR;
	char           wk10[2];
	unsigned short TADCORA;
	unsigned short TADCORB;
	unsigned short TADCOBRA;
	unsigned short TADCOBRB;
	char           wk11[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC2 : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char TPSC2 : 3;
#endif
	} BIT;
	} TCR2;
	char           wk12[38];
	unsigned short TGRE;
	unsigned short TGRF;
	char           wk13[28];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFAEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFDEN : 1;
			unsigned char NFCS : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char NFCS : 2;
			unsigned char NFDEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFAEN : 1;
#endif
	} BIT;
	} NFCR4;
} st_mtu4_t;

typedef struct st_mtu5 {
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFUEN : 1;
			unsigned char NFVEN : 1;
			unsigned char NFWEN : 1;
			unsigned char  : 1;
			unsigned char NFCS : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char NFCS : 2;
			unsigned char  : 1;
			unsigned char NFWEN : 1;
			unsigned char NFVEN : 1;
			unsigned char NFUEN : 1;
#endif
	} BIT;
	} NFCR5;
	char           wk1[490];
	unsigned short TCNTU;
	unsigned short TGRU;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char TPSC : 2;
#endif
	} BIT;
	} TCRU;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC2 : 3;
			unsigned char CKEG : 2;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char CKEG : 2;
			unsigned char TPSC2 : 3;
#endif
	} BIT;
	} TCR2U;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOC : 5;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char IOC : 5;
#endif
	} BIT;
	} TIORU;
	char           wk2[9];
	unsigned short TCNTV;
	unsigned short TGRV;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char TPSC : 2;
#endif
	} BIT;
	} TCRV;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC2 : 3;
			unsigned char CKEG : 2;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char CKEG : 2;
			unsigned char TPSC2 : 3;
#endif
	} BIT;
	} TCR2V;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOC : 5;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char IOC : 5;
#endif
	} BIT;
	} TIORV;
	char           wk3[9];
	unsigned short TCNTW;
	unsigned short TGRW;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char TPSC : 2;
#endif
	} BIT;
	} TCRW;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC2 : 3;
			unsigned char CKEG : 2;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char CKEG : 2;
			unsigned char TPSC2 : 3;
#endif
	} BIT;
	} TCR2W;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOC : 5;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char IOC : 5;
#endif
	} BIT;
	} TIORW;
	char           wk4[11];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGIE5W : 1;
			unsigned char TGIE5V : 1;
			unsigned char TGIE5U : 1;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char TGIE5U : 1;
			unsigned char TGIE5V : 1;
			unsigned char TGIE5W : 1;
#endif
	} BIT;
	} TIER;
	char           wk5[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CSTW5 : 1;
			unsigned char CSTV5 : 1;
			unsigned char CSTU5 : 1;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char CSTU5 : 1;
			unsigned char CSTV5 : 1;
			unsigned char CSTW5 : 1;
#endif
	} BIT;
	} TSTR;
	char           wk6[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CMPCLR5W : 1;
			unsigned char CMPCLR5V : 1;
			unsigned char CMPCLR5U : 1;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char CMPCLR5U : 1;
			unsigned char CMPCLR5V : 1;
			unsigned char CMPCLR5W : 1;
#endif
	} BIT;
	} TCNTCMPCLR;
} st_mtu5_t;

typedef struct st_mtu6 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC : 3;
			unsigned char CKEG : 2;
			unsigned char CCLR : 3;
#else
			unsigned char CCLR : 3;
			unsigned char CKEG : 2;
			unsigned char TPSC : 3;
#endif
	} BIT;
	} TCR;
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MD : 4;
			unsigned char BFA : 1;
			unsigned char BFB : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char BFB : 1;
			unsigned char BFA : 1;
			unsigned char MD : 4;
#endif
	} BIT;
	} TMDR1;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOA : 4;
			unsigned char IOB : 4;
#else
			unsigned char IOB : 4;
			unsigned char IOA : 4;
#endif
	} BIT;
	} TIORH;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOC : 4;
			unsigned char IOD : 4;
#else
			unsigned char IOD : 4;
			unsigned char IOC : 4;
#endif
	} BIT;
	} TIORL;
	char           wk2[2];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGIEA : 1;
			unsigned char TGIEB : 1;
			unsigned char TGIEC : 1;
			unsigned char TGIED : 1;
			unsigned char TCIEV : 1;
			unsigned char  : 2;
			unsigned char TTGE : 1;
#else
			unsigned char TTGE : 1;
			unsigned char  : 2;
			unsigned char TCIEV : 1;
			unsigned char TGIED : 1;
			unsigned char TGIEC : 1;
			unsigned char TGIEB : 1;
			unsigned char TGIEA : 1;
#endif
	} BIT;
	} TIER;
	char           wk3[7];
	unsigned short TCNT;
	char           wk4[6];
	unsigned short TGRA;
	unsigned short TGRB;
	char           wk5[8];
	unsigned short TGRC;
	unsigned short TGRD;
	char           wk6[4];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 7;
			unsigned char TCFD : 1;
#else
			unsigned char TCFD : 1;
			unsigned char  : 7;
#endif
	} BIT;
	} TSR;
	char           wk7[11];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TTSA : 1;
			unsigned char TTSB : 1;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char TTSB : 1;
			unsigned char TTSA : 1;
#endif
	} BIT;
	} TBTM;
	char           wk8[19];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC2 : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char TPSC2 : 3;
#endif
	} BIT;
	} TCR2;
	char           wk9[3];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CE2B : 1;
			unsigned char CE2A : 1;
			unsigned char CE1B : 1;
			unsigned char CE1A : 1;
			unsigned char CE0D : 1;
			unsigned char CE0C : 1;
			unsigned char CE0B : 1;
			unsigned char CE0A : 1;
#else
			unsigned char CE0A : 1;
			unsigned char CE0B : 1;
			unsigned char CE0C : 1;
			unsigned char CE0D : 1;
			unsigned char CE1A : 1;
			unsigned char CE1B : 1;
			unsigned char CE2A : 1;
			unsigned char CE2B : 1;
#endif
	} BIT;
	} TSYCR;
	char           wk10[33];
	unsigned short TGRE;
	char           wk11[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFAEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFDEN : 1;
			unsigned char NFCS : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char NFCS : 2;
			unsigned char NFDEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFAEN : 1;
#endif
	} BIT;
	} NFCR6;
} st_mtu6_t;

typedef struct st_mtu7 {
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC : 3;
			unsigned char CKEG : 2;
			unsigned char CCLR : 3;
#else
			unsigned char CCLR : 3;
			unsigned char CKEG : 2;
			unsigned char TPSC : 3;
#endif
	} BIT;
	} TCR;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MD : 4;
			unsigned char BFA : 1;
			unsigned char BFB : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char BFB : 1;
			unsigned char BFA : 1;
			unsigned char MD : 4;
#endif
	} BIT;
	} TMDR1;
	char           wk2[2];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOA : 4;
			unsigned char IOB : 4;
#else
			unsigned char IOB : 4;
			unsigned char IOA : 4;
#endif
	} BIT;
	} TIORH;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOC : 4;
			unsigned char IOD : 4;
#else
			unsigned char IOD : 4;
			unsigned char IOC : 4;
#endif
	} BIT;
	} TIORL;
	char           wk3[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGIEA : 1;
			unsigned char TGIEB : 1;
			unsigned char TGIEC : 1;
			unsigned char TGIED : 1;
			unsigned char TCIEV : 1;
			unsigned char  : 1;
			unsigned char TTGE2 : 1;
			unsigned char TTGE : 1;
#else
			unsigned char TTGE : 1;
			unsigned char TTGE2 : 1;
			unsigned char  : 1;
			unsigned char TCIEV : 1;
			unsigned char TGIED : 1;
			unsigned char TGIEC : 1;
			unsigned char TGIEB : 1;
			unsigned char TGIEA : 1;
#endif
	} BIT;
	} TIER;
	char           wk4[8];
	unsigned short TCNT;
	char           wk5[8];
	unsigned short TGRA;
	unsigned short TGRB;
	char           wk6[8];
	unsigned short TGRC;
	unsigned short TGRD;
	char           wk7[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 7;
			unsigned char TCFD : 1;
#else
			unsigned char TCFD : 1;
			unsigned char  : 7;
#endif
	} BIT;
	} TSR;
	char           wk8[11];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TTSA : 1;
			unsigned char TTSB : 1;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char TTSB : 1;
			unsigned char TTSA : 1;
#endif
	} BIT;
	} TBTM;
	char           wk9[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ITB7VE : 1;
			unsigned short ITB6AE : 1;
			unsigned short ITA7VE : 1;
			unsigned short ITA6AE : 1;
			unsigned short DT7BE : 1;
			unsigned short UT7BE : 1;
			unsigned short DT7AE : 1;
			unsigned short UT7AE : 1;
			unsigned short  : 6;
			unsigned short BF : 2;
#else
			unsigned short BF : 2;
			unsigned short  : 6;
			unsigned short UT7AE : 1;
			unsigned short DT7AE : 1;
			unsigned short UT7BE : 1;
			unsigned short DT7BE : 1;
			unsigned short ITA6AE : 1;
			unsigned short ITA7VE : 1;
			unsigned short ITB6AE : 1;
			unsigned short ITB7VE : 1;
#endif
	} BIT;
	} TADCR;
	char           wk10[2];
	unsigned short TADCORA;
	unsigned short TADCORB;
	unsigned short TADCOBRA;
	unsigned short TADCOBRB;
	char           wk11[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC2 : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char TPSC2 : 3;
#endif
	} BIT;
	} TCR2;
	char           wk12[38];
	unsigned short TGRE;
	unsigned short TGRF;
	char           wk13[28];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFAEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFDEN : 1;
			unsigned char NFCS : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char NFCS : 2;
			unsigned char NFDEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFAEN : 1;
#endif
	} BIT;
	} NFCR7;
} st_mtu7_t;

typedef struct st_mtu8 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFAEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFDEN : 1;
			unsigned char NFCS : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char NFCS : 2;
			unsigned char NFDEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFAEN : 1;
#endif
	} BIT;
	} NFCR8;
	char           wk0[871];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC : 3;
			unsigned char CKEG : 2;
			unsigned char CCLR : 3;
#else
			unsigned char CCLR : 3;
			unsigned char CKEG : 2;
			unsigned char TPSC : 3;
#endif
	} BIT;
	} TCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MD : 4;
			unsigned char BFA : 1;
			unsigned char BFB : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char BFB : 1;
			unsigned char BFA : 1;
			unsigned char MD : 4;
#endif
	} BIT;
	} TMDR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOA : 4;
			unsigned char IOB : 4;
#else
			unsigned char IOB : 4;
			unsigned char IOA : 4;
#endif
	} BIT;
	} TIORH;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOC : 4;
			unsigned char IOD : 4;
#else
			unsigned char IOD : 4;
			unsigned char IOC : 4;
#endif
	} BIT;
	} TIORL;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGIEA : 1;
			unsigned char TGIEB : 1;
			unsigned char TGIEC : 1;
			unsigned char TGIED : 1;
			unsigned char TCIEV : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char TCIEV : 1;
			unsigned char TGIED : 1;
			unsigned char TGIEC : 1;
			unsigned char TGIEB : 1;
			unsigned char TGIEA : 1;
#endif
	} BIT;
	} TIER;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC2 : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char TPSC2 : 3;
#endif
	} BIT;
	} TCR2;
	char           wk2[1];
	unsigned long  TCNT;
	unsigned long  TGRA;
	unsigned long  TGRB;
	unsigned long  TGRC;
	unsigned long  TGRD;
} st_mtu8_t;

typedef struct st_ofsm {
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MDE : 3;
			unsigned long  : 1;
			unsigned long BANKMD : 3;
			unsigned long  : 25;
#else
			unsigned long  : 25;
			unsigned long BANKMD : 3;
			unsigned long  : 1;
			unsigned long MDE : 3;
#endif
	} BIT;
	} MDE;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 1;
			unsigned long IWDTSTRT : 1;
			unsigned long IWDTTOPS : 2;
			unsigned long IWDTCKS : 4;
			unsigned long IWDTRPES : 2;
			unsigned long IWDTRPSS : 2;
			unsigned long IWDTRSTIRQS : 1;
			unsigned long  : 1;
			unsigned long IWDTSLCSTP : 1;
			unsigned long  : 2;
			unsigned long WDTSTRT : 1;
			unsigned long WDTTOPS : 2;
			unsigned long WDTCKS : 4;
			unsigned long WDTRPES : 2;
			unsigned long WDTRPSS : 2;
			unsigned long WDTRSTIRQS : 1;
			unsigned long  : 3;
#else
			unsigned long  : 3;
			unsigned long WDTRSTIRQS : 1;
			unsigned long WDTRPSS : 2;
			unsigned long WDTRPES : 2;
			unsigned long WDTCKS : 4;
			unsigned long WDTTOPS : 2;
			unsigned long WDTSTRT : 1;
			unsigned long  : 2;
			unsigned long IWDTSLCSTP : 1;
			unsigned long  : 1;
			unsigned long IWDTRSTIRQS : 1;
			unsigned long IWDTRPSS : 2;
			unsigned long IWDTRPES : 2;
			unsigned long IWDTCKS : 4;
			unsigned long IWDTTOPS : 2;
			unsigned long IWDTSTRT : 1;
			unsigned long  : 1;
#endif
	} BIT;
	} OFS0;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long VDSEL : 2;
			unsigned long LVDAS : 1;
			unsigned long  : 5;
			unsigned long HOCOEN : 1;
			unsigned long  : 23;
#else
			unsigned long  : 23;
			unsigned long HOCOEN : 1;
			unsigned long  : 5;
			unsigned long LVDAS : 1;
			unsigned long VDSEL : 2;
#endif
	} BIT;
	} OFS1;
	char           wk0[4];
	unsigned long  TMINF;
	char           wk1[12];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long BANKSWP : 3;
			unsigned long  : 29;
#else
			unsigned long  : 29;
			unsigned long BANKSWP : 3;
#endif
	} BIT;
	} BANKSEL;
	char           wk2[28];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 27;
			unsigned long SPE : 1;
			unsigned long  : 4;
#else
			unsigned long  : 4;
			unsigned long SPE : 1;
			unsigned long  : 27;
#endif
	} BIT;
	} SPCC;
	char           wk3[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 24;
			unsigned long TMEF : 3;
			unsigned long  : 1;
			unsigned long TMEFDB : 3;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long TMEFDB : 3;
			unsigned long  : 1;
			unsigned long TMEF : 3;
			unsigned long  : 24;
#endif
	} BIT;
	} TMEF;
	char           wk4[4];
	union {
		struct {
			unsigned long ID4:8;
			unsigned long ID3:8;
			unsigned long ID2:8;
			unsigned long ID1:8;
			unsigned long ID8:8;
			unsigned long ID7:8;
			unsigned long ID6:8;
			unsigned long ID5:8;
			unsigned long ID12:8;
			unsigned long ID11:8;
			unsigned long ID10:8;
			unsigned long ID9:8;
			unsigned long ID16:8;
			unsigned long ID15:8;
			unsigned long ID14:8;
			unsigned long ID13:8;
		} BIT;
	} OSIS;
	char           wk5[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long FAWS : 12;
			unsigned long  : 3;
			unsigned long FSPR : 1;
			unsigned long FAWE : 12;
			unsigned long  : 3;
			unsigned long BTFLG : 1;
#else
			unsigned long BTFLG : 1;
			unsigned long  : 3;
			unsigned long FAWE : 12;
			unsigned long FSPR : 1;
			unsigned long  : 3;
			unsigned long FAWS : 12;
#endif
	} BIT;
	} FAW;
	char           wk6[8];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CODE : 32;
#else
			unsigned long CODE : 32;
#endif
	} BIT;
	} ROMCODE;
} st_ofsm_t;

typedef struct st_pdc {
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PCKE : 1;
			unsigned long VPS : 1;
			unsigned long HPS : 1;
			unsigned long PRST : 1;
			unsigned long DFIE : 1;
			unsigned long FEIE : 1;
			unsigned long OVIE : 1;
			unsigned long UDRIE : 1;
			unsigned long VERIE : 1;
			unsigned long HERIE : 1;
			unsigned long PCKOE : 1;
			unsigned long PCKDIV : 3;
			unsigned long EDS : 1;
			unsigned long  : 17;
#else
			unsigned long  : 17;
			unsigned long EDS : 1;
			unsigned long PCKDIV : 3;
			unsigned long PCKOE : 1;
			unsigned long HERIE : 1;
			unsigned long VERIE : 1;
			unsigned long UDRIE : 1;
			unsigned long OVIE : 1;
			unsigned long FEIE : 1;
			unsigned long DFIE : 1;
			unsigned long PRST : 1;
			unsigned long HPS : 1;
			unsigned long VPS : 1;
			unsigned long PCKE : 1;
#endif
	} BIT;
	} PCCR0;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PCE : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long PCE : 1;
#endif
	} BIT;
	} PCCR1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long FBSY : 1;
			unsigned long FEMPF : 1;
			unsigned long FEF : 1;
			unsigned long OVRF : 1;
			unsigned long UDRF : 1;
			unsigned long VERF : 1;
			unsigned long HERF : 1;
			unsigned long  : 25;
#else
			unsigned long  : 25;
			unsigned long HERF : 1;
			unsigned long VERF : 1;
			unsigned long UDRF : 1;
			unsigned long OVRF : 1;
			unsigned long FEF : 1;
			unsigned long FEMPF : 1;
			unsigned long FBSY : 1;
#endif
	} BIT;
	} PCSR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long VSYNC : 1;
			unsigned long HSYNC : 1;
			unsigned long  : 30;
#else
			unsigned long  : 30;
			unsigned long HSYNC : 1;
			unsigned long VSYNC : 1;
#endif
	} BIT;
	} PCMONR;
	union {
		unsigned long LONG;
	} PCDR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long VST : 12;
			unsigned long  : 4;
			unsigned long VSZ : 12;
			unsigned long  : 4;
#else
			unsigned long  : 4;
			unsigned long VSZ : 12;
			unsigned long  : 4;
			unsigned long VST : 12;
#endif
	} BIT;
	} VCR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long HST : 12;
			unsigned long  : 4;
			unsigned long HSZ : 12;
			unsigned long  : 4;
#else
			unsigned long  : 4;
			unsigned long HSZ : 12;
			unsigned long  : 4;
			unsigned long HST : 12;
#endif
	} BIT;
	} HCR;
} st_pdc_t;

typedef struct st_pmgi {
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 8;
			unsigned long PSMCS : 6;
			unsigned long  : 1;
			unsigned long PSMDP : 1;
			unsigned long PSMHT : 3;
			unsigned long  : 1;
			unsigned long PSMCT : 3;
			unsigned long  : 9;
#else
			unsigned long  : 9;
			unsigned long PSMCT : 3;
			unsigned long  : 1;
			unsigned long PSMHT : 3;
			unsigned long PSMDP : 1;
			unsigned long  : 1;
			unsigned long PSMCS : 6;
			unsigned long  : 8;
#endif
	} BIT;
	} PMGCR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PSME : 1;
			unsigned long PSMAD : 1;
			unsigned long  : 1;
			unsigned long PDA : 5;
			unsigned long PRA : 5;
			unsigned long  : 3;
			unsigned long PRD : 16;
#else
			unsigned long PRD : 16;
			unsigned long  : 3;
			unsigned long PRA : 5;
			unsigned long PDA : 5;
			unsigned long  : 1;
			unsigned long PSMAD : 1;
			unsigned long PSME : 1;
#endif
	} BIT;
	} PSMR;
} st_pmgi_t;

typedef struct st_poe {
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short POE0M : 2;
			unsigned short  : 6;
			unsigned short PIE1 : 1;
			unsigned short  : 3;
			unsigned short POE0F : 1;
			unsigned short  : 3;
#else
			unsigned short  : 3;
			unsigned short POE0F : 1;
			unsigned short  : 3;
			unsigned short PIE1 : 1;
			unsigned short  : 6;
			unsigned short POE0M : 2;
#endif
	} BIT;
	} ICSR1;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 8;
			unsigned short OIE1 : 1;
			unsigned short OCE1 : 1;
			unsigned short  : 5;
			unsigned short OSF1 : 1;
#else
			unsigned short OSF1 : 1;
			unsigned short  : 5;
			unsigned short OCE1 : 1;
			unsigned short OIE1 : 1;
			unsigned short  : 8;
#endif
	} BIT;
	} OCSR1;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short POE4M : 2;
			unsigned short  : 6;
			unsigned short PIE2 : 1;
			unsigned short  : 3;
			unsigned short POE4F : 1;
			unsigned short  : 3;
#else
			unsigned short  : 3;
			unsigned short POE4F : 1;
			unsigned short  : 3;
			unsigned short PIE2 : 1;
			unsigned short  : 6;
			unsigned short POE4M : 2;
#endif
	} BIT;
	} ICSR2;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 8;
			unsigned short OIE2 : 1;
			unsigned short OCE2 : 1;
			unsigned short  : 5;
			unsigned short OSF2 : 1;
#else
			unsigned short OSF2 : 1;
			unsigned short  : 5;
			unsigned short OCE2 : 1;
			unsigned short OIE2 : 1;
			unsigned short  : 8;
#endif
	} BIT;
	} OCSR2;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short POE8M : 2;
			unsigned short  : 6;
			unsigned short PIE3 : 1;
			unsigned short POE8E : 1;
			unsigned short  : 2;
			unsigned short POE8F : 1;
			unsigned short  : 3;
#else
			unsigned short  : 3;
			unsigned short POE8F : 1;
			unsigned short  : 2;
			unsigned short POE8E : 1;
			unsigned short PIE3 : 1;
			unsigned short  : 6;
			unsigned short POE8M : 2;
#endif
	} BIT;
	} ICSR3;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MTUCH34HIZ : 1;
			unsigned char MTUCH67HIZ : 1;
			unsigned char MTUCH0HIZ : 1;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char MTUCH0HIZ : 1;
			unsigned char MTUCH67HIZ : 1;
			unsigned char MTUCH34HIZ : 1;
#endif
	} BIT;
	} SPOER;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MTU0AZE : 1;
			unsigned char MTU0BZE : 1;
			unsigned char MTU0CZE : 1;
			unsigned char MTU0DZE : 1;
			unsigned char  : 4;
#else
			unsigned char  : 4;
			unsigned char MTU0DZE : 1;
			unsigned char MTU0CZE : 1;
			unsigned char MTU0BZE : 1;
			unsigned char MTU0AZE : 1;
#endif
	} BIT;
	} POECR1;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short MTU7BDZE : 1;
			unsigned short MTU7ACZE : 1;
			unsigned short MTU6BDZE : 1;
			unsigned short  : 5;
			unsigned short MTU4BDZE : 1;
			unsigned short MTU4ACZE : 1;
			unsigned short MTU3BDZE : 1;
			unsigned short  : 5;
#else
			unsigned short  : 5;
			unsigned short MTU3BDZE : 1;
			unsigned short MTU4ACZE : 1;
			unsigned short MTU4BDZE : 1;
			unsigned short  : 5;
			unsigned short MTU6BDZE : 1;
			unsigned short MTU7ACZE : 1;
			unsigned short MTU7BDZE : 1;
#endif
	} BIT;
	} POECR2;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 2;
			unsigned short IC2ADDMT34ZE : 1;
			unsigned short IC3ADDMT34ZE : 1;
			unsigned short IC4ADDMT34ZE : 1;
			unsigned short IC5ADDMT34ZE : 1;
			unsigned short  : 3;
			unsigned short IC1ADDMT67ZE : 1;
			unsigned short  : 1;
			unsigned short IC3ADDMT67ZE : 1;
			unsigned short IC4ADDMT67ZE : 1;
			unsigned short IC5ADDMT67ZE : 1;
			unsigned short  : 2;
#else
			unsigned short  : 2;
			unsigned short IC5ADDMT67ZE : 1;
			unsigned short IC4ADDMT67ZE : 1;
			unsigned short IC3ADDMT67ZE : 1;
			unsigned short  : 1;
			unsigned short IC1ADDMT67ZE : 1;
			unsigned short  : 3;
			unsigned short IC5ADDMT34ZE : 1;
			unsigned short IC4ADDMT34ZE : 1;
			unsigned short IC3ADDMT34ZE : 1;
			unsigned short IC2ADDMT34ZE : 1;
			unsigned short  : 2;
#endif
	} BIT;
	} POECR4;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 1;
			unsigned short IC1ADDMT0ZE : 1;
			unsigned short IC2ADDMT0ZE : 1;
			unsigned short  : 1;
			unsigned short IC4ADDMT0ZE : 1;
			unsigned short IC5ADDMT0ZE : 1;
			unsigned short  : 10;
#else
			unsigned short  : 10;
			unsigned short IC5ADDMT0ZE : 1;
			unsigned short IC4ADDMT0ZE : 1;
			unsigned short  : 1;
			unsigned short IC2ADDMT0ZE : 1;
			unsigned short IC1ADDMT0ZE : 1;
			unsigned short  : 1;
#endif
	} BIT;
	} POECR5;
	char           wk1[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short POE10M : 2;
			unsigned short  : 6;
			unsigned short PIE4 : 1;
			unsigned short POE10E : 1;
			unsigned short  : 2;
			unsigned short POE10F : 1;
			unsigned short  : 3;
#else
			unsigned short  : 3;
			unsigned short POE10F : 1;
			unsigned short  : 2;
			unsigned short POE10E : 1;
			unsigned short PIE4 : 1;
			unsigned short  : 6;
			unsigned short POE10M : 2;
#endif
	} BIT;
	} ICSR4;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short POE11M : 2;
			unsigned short  : 6;
			unsigned short PIE5 : 1;
			unsigned short POE11E : 1;
			unsigned short  : 2;
			unsigned short POE11F : 1;
			unsigned short  : 3;
#else
			unsigned short  : 3;
			unsigned short POE11F : 1;
			unsigned short  : 2;
			unsigned short POE11E : 1;
			unsigned short PIE5 : 1;
			unsigned short  : 6;
			unsigned short POE11M : 2;
#endif
	} BIT;
	} ICSR5;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short OLSG0A : 1;
			unsigned short OLSG0B : 1;
			unsigned short OLSG1A : 1;
			unsigned short OLSG1B : 1;
			unsigned short OLSG2A : 1;
			unsigned short OLSG2B : 1;
			unsigned short  : 1;
			unsigned short OLSEN : 1;
			unsigned short  : 8;
#else
			unsigned short  : 8;
			unsigned short OLSEN : 1;
			unsigned short  : 1;
			unsigned short OLSG2B : 1;
			unsigned short OLSG2A : 1;
			unsigned short OLSG1B : 1;
			unsigned short OLSG1A : 1;
			unsigned short OLSG0B : 1;
			unsigned short OLSG0A : 1;
#endif
	} BIT;
	} ALR1;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 9;
			unsigned short OSTSTE : 1;
			unsigned short  : 2;
			unsigned short OSTSTF : 1;
			unsigned short  : 3;
#else
			unsigned short  : 3;
			unsigned short OSTSTF : 1;
			unsigned short  : 2;
			unsigned short OSTSTE : 1;
			unsigned short  : 9;
#endif
	} BIT;
	} ICSR6;
	char           wk2[6];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char M0ASEL : 4;
			unsigned char M0BSEL : 4;
#else
			unsigned char M0BSEL : 4;
			unsigned char M0ASEL : 4;
#endif
	} BIT;
	} M0SELR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char M0CSEL : 4;
			unsigned char M0DSEL : 4;
#else
			unsigned char M0DSEL : 4;
			unsigned char M0CSEL : 4;
#endif
	} BIT;
	} M0SELR2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char M3BSEL : 4;
			unsigned char M3DSEL : 4;
#else
			unsigned char M3DSEL : 4;
			unsigned char M3BSEL : 4;
#endif
	} BIT;
	} M3SELR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char M4ASEL : 4;
			unsigned char M4CSEL : 4;
#else
			unsigned char M4CSEL : 4;
			unsigned char M4ASEL : 4;
#endif
	} BIT;
	} M4SELR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char M4BSEL : 4;
			unsigned char M4DSEL : 4;
#else
			unsigned char M4DSEL : 4;
			unsigned char M4BSEL : 4;
#endif
	} BIT;
	} M4SELR2;
	char           wk3[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char M6BSEL : 4;
			unsigned char M6DSEL : 4;
#else
			unsigned char M6DSEL : 4;
			unsigned char M6BSEL : 4;
#endif
	} BIT;
	} M6SELR;
} st_poe_t;

typedef struct st_poeg {
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PIDF : 1;
			unsigned long IOCF : 1;
			unsigned long OSTPF : 1;
			unsigned long SSF : 1;
			unsigned long PIDE : 1;
			unsigned long IOCE : 1;
			unsigned long OSTPE : 1;
			unsigned long  : 9;
			unsigned long ST : 1;
			unsigned long  : 11;
			unsigned long INV : 1;
			unsigned long NFEN : 1;
			unsigned long NFCS : 2;
#else
			unsigned long NFCS : 2;
			unsigned long NFEN : 1;
			unsigned long INV : 1;
			unsigned long  : 11;
			unsigned long ST : 1;
			unsigned long  : 9;
			unsigned long OSTPE : 1;
			unsigned long IOCE : 1;
			unsigned long PIDE : 1;
			unsigned long SSF : 1;
			unsigned long OSTPF : 1;
			unsigned long IOCF : 1;
			unsigned long PIDF : 1;
#endif
	} BIT;
	} POEGGA;
	char           wk0[252];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PIDF : 1;
			unsigned long IOCF : 1;
			unsigned long OSTPF : 1;
			unsigned long SSF : 1;
			unsigned long PIDE : 1;
			unsigned long IOCE : 1;
			unsigned long OSTPE : 1;
			unsigned long  : 9;
			unsigned long ST : 1;
			unsigned long  : 11;
			unsigned long INV : 1;
			unsigned long NFEN : 1;
			unsigned long NFCS : 2;
#else
			unsigned long NFCS : 2;
			unsigned long NFEN : 1;
			unsigned long INV : 1;
			unsigned long  : 11;
			unsigned long ST : 1;
			unsigned long  : 9;
			unsigned long OSTPE : 1;
			unsigned long IOCE : 1;
			unsigned long PIDE : 1;
			unsigned long SSF : 1;
			unsigned long OSTPF : 1;
			unsigned long IOCF : 1;
			unsigned long PIDF : 1;
#endif
	} BIT;
	} POEGGB;
	char           wk1[252];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PIDF : 1;
			unsigned long IOCF : 1;
			unsigned long OSTPF : 1;
			unsigned long SSF : 1;
			unsigned long PIDE : 1;
			unsigned long IOCE : 1;
			unsigned long OSTPE : 1;
			unsigned long  : 9;
			unsigned long ST : 1;
			unsigned long  : 11;
			unsigned long INV : 1;
			unsigned long NFEN : 1;
			unsigned long NFCS : 2;
#else
			unsigned long NFCS : 2;
			unsigned long NFEN : 1;
			unsigned long INV : 1;
			unsigned long  : 11;
			unsigned long ST : 1;
			unsigned long  : 9;
			unsigned long OSTPE : 1;
			unsigned long IOCE : 1;
			unsigned long PIDE : 1;
			unsigned long SSF : 1;
			unsigned long OSTPF : 1;
			unsigned long IOCF : 1;
			unsigned long PIDF : 1;
#endif
	} BIT;
	} POEGGC;
	char           wk2[252];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PIDF : 1;
			unsigned long IOCF : 1;
			unsigned long OSTPF : 1;
			unsigned long SSF : 1;
			unsigned long PIDE : 1;
			unsigned long IOCE : 1;
			unsigned long OSTPE : 1;
			unsigned long  : 9;
			unsigned long ST : 1;
			unsigned long  : 11;
			unsigned long INV : 1;
			unsigned long NFEN : 1;
			unsigned long NFCS : 2;
#else
			unsigned long NFCS : 2;
			unsigned long NFEN : 1;
			unsigned long INV : 1;
			unsigned long  : 11;
			unsigned long ST : 1;
			unsigned long  : 9;
			unsigned long OSTPE : 1;
			unsigned long IOCE : 1;
			unsigned long PIDE : 1;
			unsigned long SSF : 1;
			unsigned long OSTPF : 1;
			unsigned long IOCF : 1;
			unsigned long PIDF : 1;
#endif
	} BIT;
	} POEGGD;
} st_poeg_t;

typedef struct st_port0 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char  : 1;
			unsigned char B5 : 1;
			unsigned char  : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char  : 1;
			unsigned char B5 : 1;
			unsigned char  : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char  : 1;
			unsigned char B5 : 1;
			unsigned char  : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char  : 1;
			unsigned char B5 : 1;
			unsigned char  : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char  : 1;
			unsigned char B5 : 1;
			unsigned char  : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char  : 1;
			unsigned char B5 : 1;
			unsigned char  : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char  : 1;
			unsigned char B5 : 1;
			unsigned char  : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char  : 1;
			unsigned char B5 : 1;
			unsigned char  : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 2;
			unsigned char B2 : 1;
			unsigned char  : 3;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 3;
			unsigned char B2 : 1;
			unsigned char  : 2;
#endif
	} BIT;
	} ODR1;
	char           wk4[62];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char  : 1;
			unsigned char B5 : 1;
			unsigned char  : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char  : 1;
			unsigned char B5 : 1;
			unsigned char  : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR;
	char           wk6[71];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_port0_t;

typedef struct st_port1 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[32];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[61];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char  : 1;
#endif
	} BIT;
	} DSCR;
	char           wk6[71];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char  : 2;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char  : 2;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char  : 1;
#endif
	} BIT;
	} DSCR2;
} st_port1_t;

typedef struct st_port2 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[33];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[60];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 7;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char  : 7;
#endif
	} BIT;
	} DSCR;
	char           wk6[71];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char  : 3;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char  : 3;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_port2_t;

typedef struct st_port3 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[34];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 3;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 3;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[59];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[103];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_port3_t;

typedef struct st_port4 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[35];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[58];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
} st_port4_t;

typedef struct st_port5 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[36];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[57];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR;
	char           wk6[71];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_port5_t;

typedef struct st_port6 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[37];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[56];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[103];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_port6_t;

typedef struct st_port7 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[38];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[55];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 2;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 2;
#endif
	} BIT;
	} DSCR;
	char           wk6[71];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_port7_t;

typedef struct st_port8 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[39];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[54];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR;
	char           wk6[71];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char  : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char  : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_port8_t;

typedef struct st_port9 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[40];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[53];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR;
	char           wk6[71];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_port9_t;

typedef struct st_porta {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[41];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[52];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR;
	char           wk6[71];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_porta_t;

typedef struct st_portb {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[42];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[51];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR;
	char           wk6[71];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_portb_t;

typedef struct st_portc {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[43];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[50];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR;
	char           wk6[71];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_portc_t;

typedef struct st_portd {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[44];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[49];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR;
	char           wk6[71];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_portd_t;

typedef struct st_porte {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[45];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[48];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR;
	char           wk6[71];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_porte_t;

typedef struct st_portf {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[46];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[47];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
} st_portf_t;

typedef struct st_portg {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[47];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[46];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR;
	char           wk6[71];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_portg_t;

typedef struct st_porth {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[48];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[45];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR;
	char           wk6[71];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_porth_t;

typedef struct st_portj {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char  : 1;
			unsigned char B5 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char B5 : 1;
			unsigned char  : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char  : 1;
			unsigned char B5 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char B5 : 1;
			unsigned char  : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char  : 1;
			unsigned char B5 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char B5 : 1;
			unsigned char  : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char  : 1;
			unsigned char B5 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char B5 : 1;
			unsigned char  : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[49];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 2;
			unsigned char B2 : 1;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char B2 : 1;
			unsigned char  : 2;
#endif
	} BIT;
	} ODR1;
	char           wk4[44];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char  : 1;
			unsigned char B5 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char B5 : 1;
			unsigned char  : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR;
	char           wk6[71];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_portj_t;

typedef struct st_portk {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[50];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[43];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR;
	char           wk6[71];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_portk_t;

typedef struct st_portl {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[51];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[42];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR;
	char           wk6[71];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_portl_t;

typedef struct st_portm {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[52];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[41];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR;
	char           wk6[71];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_portm_t;

typedef struct st_portn {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[53];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[40];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR;
	char           wk6[71];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_portn_t;

typedef struct st_portq {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PMR;
	char           wk3[54];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char B6 : 1;
			unsigned char  : 1;
			unsigned char B4 : 1;
			unsigned char  : 1;
			unsigned char B2 : 1;
			unsigned char  : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} ODR1;
	char           wk4[39];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR;
	char           wk6[71];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char B0 : 1;
			unsigned char B1 : 1;
			unsigned char B2 : 1;
			unsigned char B3 : 1;
			unsigned char B4 : 1;
			unsigned char B5 : 1;
			unsigned char B6 : 1;
			unsigned char B7 : 1;
#else
			unsigned char B7 : 1;
			unsigned char B6 : 1;
			unsigned char B5 : 1;
			unsigned char B4 : 1;
			unsigned char B3 : 1;
			unsigned char B2 : 1;
			unsigned char B1 : 1;
			unsigned char B0 : 1;
#endif
	} BIT;
	} DSCR2;
} st_portq_t;

typedef struct st_ppg0 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char G0CMS : 2;
			unsigned char G1CMS : 2;
			unsigned char G2CMS : 2;
			unsigned char G3CMS : 2;
#else
			unsigned char G3CMS : 2;
			unsigned char G2CMS : 2;
			unsigned char G1CMS : 2;
			unsigned char G0CMS : 2;
#endif
	} BIT;
	} PCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char G0NOV : 1;
			unsigned char G1NOV : 1;
			unsigned char G2NOV : 1;
			unsigned char G3NOV : 1;
			unsigned char G0INV : 1;
			unsigned char G1INV : 1;
			unsigned char G2INV : 1;
			unsigned char G3INV : 1;
#else
			unsigned char G3INV : 1;
			unsigned char G2INV : 1;
			unsigned char G1INV : 1;
			unsigned char G0INV : 1;
			unsigned char G3NOV : 1;
			unsigned char G2NOV : 1;
			unsigned char G1NOV : 1;
			unsigned char G0NOV : 1;
#endif
	} BIT;
	} PMR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NDER8 : 1;
			unsigned char NDER9 : 1;
			unsigned char NDER10 : 1;
			unsigned char NDER11 : 1;
			unsigned char NDER12 : 1;
			unsigned char NDER13 : 1;
			unsigned char NDER14 : 1;
			unsigned char NDER15 : 1;
#else
			unsigned char NDER15 : 1;
			unsigned char NDER14 : 1;
			unsigned char NDER13 : 1;
			unsigned char NDER12 : 1;
			unsigned char NDER11 : 1;
			unsigned char NDER10 : 1;
			unsigned char NDER9 : 1;
			unsigned char NDER8 : 1;
#endif
	} BIT;
	} NDERH;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NDER0 : 1;
			unsigned char NDER1 : 1;
			unsigned char NDER2 : 1;
			unsigned char NDER3 : 1;
			unsigned char NDER4 : 1;
			unsigned char NDER5 : 1;
			unsigned char NDER6 : 1;
			unsigned char NDER7 : 1;
#else
			unsigned char NDER7 : 1;
			unsigned char NDER6 : 1;
			unsigned char NDER5 : 1;
			unsigned char NDER4 : 1;
			unsigned char NDER3 : 1;
			unsigned char NDER2 : 1;
			unsigned char NDER1 : 1;
			unsigned char NDER0 : 1;
#endif
	} BIT;
	} NDERL;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char POD8 : 1;
			unsigned char POD9 : 1;
			unsigned char POD10 : 1;
			unsigned char POD11 : 1;
			unsigned char POD12 : 1;
			unsigned char POD13 : 1;
			unsigned char POD14 : 1;
			unsigned char POD15 : 1;
#else
			unsigned char POD15 : 1;
			unsigned char POD14 : 1;
			unsigned char POD13 : 1;
			unsigned char POD12 : 1;
			unsigned char POD11 : 1;
			unsigned char POD10 : 1;
			unsigned char POD9 : 1;
			unsigned char POD8 : 1;
#endif
	} BIT;
	} PODRH;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char POD0 : 1;
			unsigned char POD1 : 1;
			unsigned char POD2 : 1;
			unsigned char POD3 : 1;
			unsigned char POD4 : 1;
			unsigned char POD5 : 1;
			unsigned char POD6 : 1;
			unsigned char POD7 : 1;
#else
			unsigned char POD7 : 1;
			unsigned char POD6 : 1;
			unsigned char POD5 : 1;
			unsigned char POD4 : 1;
			unsigned char POD3 : 1;
			unsigned char POD2 : 1;
			unsigned char POD1 : 1;
			unsigned char POD0 : 1;
#endif
	} BIT;
	} PODRL;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NDR8 : 1;
			unsigned char NDR9 : 1;
			unsigned char NDR10 : 1;
			unsigned char NDR11 : 1;
			unsigned char NDR12 : 1;
			unsigned char NDR13 : 1;
			unsigned char NDR14 : 1;
			unsigned char NDR15 : 1;
#else
			unsigned char NDR15 : 1;
			unsigned char NDR14 : 1;
			unsigned char NDR13 : 1;
			unsigned char NDR12 : 1;
			unsigned char NDR11 : 1;
			unsigned char NDR10 : 1;
			unsigned char NDR9 : 1;
			unsigned char NDR8 : 1;
#endif
	} BIT;
	} NDRH;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NDR0 : 1;
			unsigned char NDR1 : 1;
			unsigned char NDR2 : 1;
			unsigned char NDR3 : 1;
			unsigned char NDR4 : 1;
			unsigned char NDR5 : 1;
			unsigned char NDR6 : 1;
			unsigned char NDR7 : 1;
#else
			unsigned char NDR7 : 1;
			unsigned char NDR6 : 1;
			unsigned char NDR5 : 1;
			unsigned char NDR4 : 1;
			unsigned char NDR3 : 1;
			unsigned char NDR2 : 1;
			unsigned char NDR1 : 1;
			unsigned char NDR0 : 1;
#endif
	} BIT;
	} NDRL;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NDR8 : 1;
			unsigned char NDR9 : 1;
			unsigned char NDR10 : 1;
			unsigned char NDR11 : 1;
			unsigned char  : 4;
#else
			unsigned char  : 4;
			unsigned char NDR11 : 1;
			unsigned char NDR10 : 1;
			unsigned char NDR9 : 1;
			unsigned char NDR8 : 1;
#endif
	} BIT;
	} NDRH2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NDR0 : 1;
			unsigned char NDR1 : 1;
			unsigned char NDR2 : 1;
			unsigned char NDR3 : 1;
			unsigned char  : 4;
#else
			unsigned char  : 4;
			unsigned char NDR3 : 1;
			unsigned char NDR2 : 1;
			unsigned char NDR1 : 1;
			unsigned char NDR0 : 1;
#endif
	} BIT;
	} NDRL2;
} st_ppg0_t;

typedef struct st_ppg1 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PTRSL : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char PTRSL : 1;
#endif
	} BIT;
	} PTRSLR;
	char           wk0[5];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char G0CMS : 2;
			unsigned char G1CMS : 2;
			unsigned char G2CMS : 2;
			unsigned char G3CMS : 2;
#else
			unsigned char G3CMS : 2;
			unsigned char G2CMS : 2;
			unsigned char G1CMS : 2;
			unsigned char G0CMS : 2;
#endif
	} BIT;
	} PCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char G0NOV : 1;
			unsigned char G1NOV : 1;
			unsigned char G2NOV : 1;
			unsigned char G3NOV : 1;
			unsigned char G0INV : 1;
			unsigned char G1INV : 1;
			unsigned char G2INV : 1;
			unsigned char G3INV : 1;
#else
			unsigned char G3INV : 1;
			unsigned char G2INV : 1;
			unsigned char G1INV : 1;
			unsigned char G0INV : 1;
			unsigned char G3NOV : 1;
			unsigned char G2NOV : 1;
			unsigned char G1NOV : 1;
			unsigned char G0NOV : 1;
#endif
	} BIT;
	} PMR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NDER24 : 1;
			unsigned char NDER25 : 1;
			unsigned char NDER26 : 1;
			unsigned char NDER27 : 1;
			unsigned char NDER28 : 1;
			unsigned char NDER29 : 1;
			unsigned char NDER30 : 1;
			unsigned char NDER31 : 1;
#else
			unsigned char NDER31 : 1;
			unsigned char NDER30 : 1;
			unsigned char NDER29 : 1;
			unsigned char NDER28 : 1;
			unsigned char NDER27 : 1;
			unsigned char NDER26 : 1;
			unsigned char NDER25 : 1;
			unsigned char NDER24 : 1;
#endif
	} BIT;
	} NDERH;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NDER16 : 1;
			unsigned char NDER17 : 1;
			unsigned char NDER18 : 1;
			unsigned char NDER19 : 1;
			unsigned char NDER20 : 1;
			unsigned char NDER21 : 1;
			unsigned char NDER22 : 1;
			unsigned char NDER23 : 1;
#else
			unsigned char NDER23 : 1;
			unsigned char NDER22 : 1;
			unsigned char NDER21 : 1;
			unsigned char NDER20 : 1;
			unsigned char NDER19 : 1;
			unsigned char NDER18 : 1;
			unsigned char NDER17 : 1;
			unsigned char NDER16 : 1;
#endif
	} BIT;
	} NDERL;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char POD24 : 1;
			unsigned char POD25 : 1;
			unsigned char POD26 : 1;
			unsigned char POD27 : 1;
			unsigned char POD28 : 1;
			unsigned char POD29 : 1;
			unsigned char POD30 : 1;
			unsigned char POD31 : 1;
#else
			unsigned char POD31 : 1;
			unsigned char POD30 : 1;
			unsigned char POD29 : 1;
			unsigned char POD28 : 1;
			unsigned char POD27 : 1;
			unsigned char POD26 : 1;
			unsigned char POD25 : 1;
			unsigned char POD24 : 1;
#endif
	} BIT;
	} PODRH;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char POD16 : 1;
			unsigned char POD17 : 1;
			unsigned char POD18 : 1;
			unsigned char POD19 : 1;
			unsigned char POD20 : 1;
			unsigned char POD21 : 1;
			unsigned char POD22 : 1;
			unsigned char POD23 : 1;
#else
			unsigned char POD23 : 1;
			unsigned char POD22 : 1;
			unsigned char POD21 : 1;
			unsigned char POD20 : 1;
			unsigned char POD19 : 1;
			unsigned char POD18 : 1;
			unsigned char POD17 : 1;
			unsigned char POD16 : 1;
#endif
	} BIT;
	} PODRL;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NDR24 : 1;
			unsigned char NDR25 : 1;
			unsigned char NDR26 : 1;
			unsigned char NDR27 : 1;
			unsigned char NDR28 : 1;
			unsigned char NDR29 : 1;
			unsigned char NDR30 : 1;
			unsigned char NDR31 : 1;
#else
			unsigned char NDR31 : 1;
			unsigned char NDR30 : 1;
			unsigned char NDR29 : 1;
			unsigned char NDR28 : 1;
			unsigned char NDR27 : 1;
			unsigned char NDR26 : 1;
			unsigned char NDR25 : 1;
			unsigned char NDR24 : 1;
#endif
	} BIT;
	} NDRH;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NDR16 : 1;
			unsigned char NDR17 : 1;
			unsigned char NDR18 : 1;
			unsigned char NDR19 : 1;
			unsigned char NDR20 : 1;
			unsigned char NDR21 : 1;
			unsigned char NDR22 : 1;
			unsigned char NDR23 : 1;
#else
			unsigned char NDR23 : 1;
			unsigned char NDR22 : 1;
			unsigned char NDR21 : 1;
			unsigned char NDR20 : 1;
			unsigned char NDR19 : 1;
			unsigned char NDR18 : 1;
			unsigned char NDR17 : 1;
			unsigned char NDR16 : 1;
#endif
	} BIT;
	} NDRL;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NDR24 : 1;
			unsigned char NDR25 : 1;
			unsigned char NDR26 : 1;
			unsigned char NDR27 : 1;
			unsigned char  : 4;
#else
			unsigned char  : 4;
			unsigned char NDR27 : 1;
			unsigned char NDR26 : 1;
			unsigned char NDR25 : 1;
			unsigned char NDR24 : 1;
#endif
	} BIT;
	} NDRH2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NDR16 : 1;
			unsigned char NDR17 : 1;
			unsigned char NDR18 : 1;
			unsigned char NDR19 : 1;
			unsigned char  : 4;
#else
			unsigned char  : 4;
			unsigned char NDR19 : 1;
			unsigned char NDR18 : 1;
			unsigned char NDR17 : 1;
			unsigned char NDR16 : 1;
#endif
	} BIT;
	} NDRL2;
} st_ppg1_t;

typedef struct st_ptpedmac {
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long SWR : 1;
			unsigned long  : 3;
			unsigned long DL : 2;
			unsigned long DE : 1;
			unsigned long  : 25;
#else
			unsigned long  : 25;
			unsigned long DE : 1;
			unsigned long DL : 2;
			unsigned long  : 3;
			unsigned long SWR : 1;
#endif
	} BIT;
	} EDMR;
	char           wk0[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TR : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long TR : 1;
#endif
	} BIT;
	} EDTRR;
	char           wk1[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RR : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long RR : 1;
#endif
	} BIT;
	} EDRRR;
	char           wk2[4];
	void          *TDLAR;
	char           wk3[4];
	void          *RDLAR;
	char           wk4[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TYPE : 4;
			unsigned long PVER : 1;
			unsigned long  : 2;
			unsigned long RPORT : 1;
			unsigned long MACE : 1;
			unsigned long  : 7;
			unsigned long RFOF : 1;
			unsigned long RDE : 1;
			unsigned long FR : 1;
			unsigned long TFUF : 1;
			unsigned long TDE : 1;
			unsigned long TC : 1;
			unsigned long  : 2;
			unsigned long RFCOF : 1;
			unsigned long  : 1;
			unsigned long TABT : 1;
			unsigned long  : 3;
			unsigned long TWB : 1;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long TWB : 1;
			unsigned long  : 3;
			unsigned long TABT : 1;
			unsigned long  : 1;
			unsigned long RFCOF : 1;
			unsigned long  : 2;
			unsigned long TC : 1;
			unsigned long TDE : 1;
			unsigned long TFUF : 1;
			unsigned long FR : 1;
			unsigned long RDE : 1;
			unsigned long RFOF : 1;
			unsigned long  : 7;
			unsigned long MACE : 1;
			unsigned long RPORT : 1;
			unsigned long  : 2;
			unsigned long PVER : 1;
			unsigned long TYPE : 4;
#endif
	} BIT;
	} EESR;
	char           wk5[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 4;
			unsigned long PVERIP : 1;
			unsigned long  : 2;
			unsigned long RPORTIP : 1;
			unsigned long MACEIP : 1;
			unsigned long  : 7;
			unsigned long RFOFIP : 1;
			unsigned long RDEIP : 1;
			unsigned long FRIP : 1;
			unsigned long TFUFIP : 1;
			unsigned long TDEIP : 1;
			unsigned long TCIP : 1;
			unsigned long  : 2;
			unsigned long RFCOFIP : 1;
			unsigned long  : 1;
			unsigned long TABTIP : 1;
			unsigned long  : 3;
			unsigned long TWBIP : 1;
			unsigned long  : 1;
#else
			unsigned long  : 1;
			unsigned long TWBIP : 1;
			unsigned long  : 3;
			unsigned long TABTIP : 1;
			unsigned long  : 1;
			unsigned long RFCOFIP : 1;
			unsigned long  : 2;
			unsigned long TCIP : 1;
			unsigned long TDEIP : 1;
			unsigned long TFUFIP : 1;
			unsigned long FRIP : 1;
			unsigned long RDEIP : 1;
			unsigned long RFOFIP : 1;
			unsigned long  : 7;
			unsigned long MACEIP : 1;
			unsigned long RPORTIP : 1;
			unsigned long  : 2;
			unsigned long PVERIP : 1;
			unsigned long  : 4;
#endif
	} BIT;
	} EESIPR;
	char           wk6[12];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MFC : 16;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long MFC : 16;
#endif
	} BIT;
	} RMFCR;
	char           wk7[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TFT : 11;
			unsigned long  : 21;
#else
			unsigned long  : 21;
			unsigned long TFT : 11;
#endif
	} BIT;
	} TFTR;
	char           wk8[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RFD : 5;
			unsigned long  : 3;
			unsigned long TFD : 5;
			unsigned long  : 19;
#else
			unsigned long  : 19;
			unsigned long TFD : 5;
			unsigned long  : 3;
			unsigned long RFD : 5;
#endif
	} BIT;
	} FDR;
	char           wk9[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RNR : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long RNR : 1;
#endif
	} BIT;
	} RMCR;
	char           wk10[8];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long UNDER : 16;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long UNDER : 16;
#endif
	} BIT;
	} TFUCR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long OVER : 16;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long OVER : 16;
#endif
	} BIT;
	} RFOCR;
	char           wk11[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RFDO : 3;
			unsigned long  : 13;
			unsigned long RFFO : 3;
			unsigned long  : 13;
#else
			unsigned long  : 13;
			unsigned long RFFO : 3;
			unsigned long  : 13;
			unsigned long RFDO : 3;
#endif
	} BIT;
	} FCFTR;
	char           wk12[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PADR : 6;
			unsigned long  : 10;
			unsigned long PADS : 2;
			unsigned long  : 14;
#else
			unsigned long  : 14;
			unsigned long PADS : 2;
			unsigned long  : 10;
			unsigned long PADR : 6;
#endif
	} BIT;
	} RPADIR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long TIS : 1;
			unsigned long  : 3;
			unsigned long TIM : 1;
			unsigned long  : 27;
#else
			unsigned long  : 27;
			unsigned long TIM : 1;
			unsigned long  : 3;
			unsigned long TIS : 1;
#endif
	} BIT;
	} TRIMD;
	char           wk13[72];
	void          *RBWAR;
	void          *RDFAR;
	char           wk14[4];
	void          *TBRAR;
	void          *TDFAR;
} st_ptpedmac_t;

typedef struct st_qspi {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 1;
			unsigned char SPSSLIE : 1;
			unsigned char  : 1;
			unsigned char MSTR : 1;
			unsigned char  : 1;
			unsigned char SPTIE : 1;
			unsigned char SPE : 1;
			unsigned char SPRIE : 1;
#else
			unsigned char SPRIE : 1;
			unsigned char SPE : 1;
			unsigned char SPTIE : 1;
			unsigned char  : 1;
			unsigned char MSTR : 1;
			unsigned char  : 1;
			unsigned char SPSSLIE : 1;
			unsigned char  : 1;
#endif
	} BIT;
	} SPCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SSLP : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char SSLP : 1;
#endif
	} BIT;
	} SSLP;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SPLP : 1;
			unsigned char IO2FV : 1;
			unsigned char IO3FV : 1;
			unsigned char  : 1;
			unsigned char MOIFV : 1;
			unsigned char MOIFE : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char MOIFE : 1;
			unsigned char MOIFV : 1;
			unsigned char  : 1;
			unsigned char IO3FV : 1;
			unsigned char IO2FV : 1;
			unsigned char SPLP : 1;
#endif
	} BIT;
	} SPPCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 4;
			unsigned char SPSSLF : 1;
			unsigned char SPTEF : 1;
			unsigned char TREND : 1;
			unsigned char SPRFF : 1;
#else
			unsigned char SPRFF : 1;
			unsigned char TREND : 1;
			unsigned char SPTEF : 1;
			unsigned char SPSSLF : 1;
			unsigned char  : 4;
#endif
	} BIT;
	} SPSR;
	union {
		unsigned long LONG;
		struct {
			unsigned short H;
		} WORD;
		struct {
			unsigned char HH;
		} BYTE;
	} SPDR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SPSC : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char SPSC : 2;
#endif
	} BIT;
	} SPSCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SPSS : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char SPSS : 2;
#endif
	} BIT;
	} SPSSR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SPBR0 : 1;
			unsigned char SPBR1 : 1;
			unsigned char SPBR2 : 1;
			unsigned char SPBR3 : 1;
			unsigned char SPBR4 : 1;
			unsigned char SPBR5 : 1;
			unsigned char SPBR6 : 1;
			unsigned char SPBR7 : 1;
#else
			unsigned char SPBR7 : 1;
			unsigned char SPBR6 : 1;
			unsigned char SPBR5 : 1;
			unsigned char SPBR4 : 1;
			unsigned char SPBR3 : 1;
			unsigned char SPBR2 : 1;
			unsigned char SPBR1 : 1;
			unsigned char SPBR0 : 1;
#endif
	} BIT;
	} SPBR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 7;
			unsigned char TXDMY : 1;
#else
			unsigned char TXDMY : 1;
			unsigned char  : 7;
#endif
	} BIT;
	} SPDCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SCKDL : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char SCKDL : 3;
#endif
	} BIT;
	} SPCKD;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLNDL : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char SLNDL : 3;
#endif
	} BIT;
	} SSLND;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SPNDL : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char SPNDL : 3;
#endif
	} BIT;
	} SPND;
	char           wk0[1];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CPHA : 1;
			unsigned short CPOL : 1;
			unsigned short BRDV : 2;
			unsigned short SPRW : 1;
			unsigned short SPIMOD : 2;
			unsigned short SSLKP : 1;
			unsigned short SPB : 4;
			unsigned short LSBF : 1;
			unsigned short SPNDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SCKDEN : 1;
#else
			unsigned short SCKDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SPNDEN : 1;
			unsigned short LSBF : 1;
			unsigned short SPB : 4;
			unsigned short SSLKP : 1;
			unsigned short SPIMOD : 2;
			unsigned short SPRW : 1;
			unsigned short BRDV : 2;
			unsigned short CPOL : 1;
			unsigned short CPHA : 1;
#endif
	} BIT;
	} SPCMD0;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CPHA : 1;
			unsigned short CPOL : 1;
			unsigned short BRDV : 2;
			unsigned short SPRW : 1;
			unsigned short SPIMOD : 2;
			unsigned short SSLKP : 1;
			unsigned short SPB : 4;
			unsigned short LSBF : 1;
			unsigned short SPNDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SCKDEN : 1;
#else
			unsigned short SCKDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SPNDEN : 1;
			unsigned short LSBF : 1;
			unsigned short SPB : 4;
			unsigned short SSLKP : 1;
			unsigned short SPIMOD : 2;
			unsigned short SPRW : 1;
			unsigned short BRDV : 2;
			unsigned short CPOL : 1;
			unsigned short CPHA : 1;
#endif
	} BIT;
	} SPCMD1;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CPHA : 1;
			unsigned short CPOL : 1;
			unsigned short BRDV : 2;
			unsigned short SPRW : 1;
			unsigned short SPIMOD : 2;
			unsigned short SSLKP : 1;
			unsigned short SPB : 4;
			unsigned short LSBF : 1;
			unsigned short SPNDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SCKDEN : 1;
#else
			unsigned short SCKDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SPNDEN : 1;
			unsigned short LSBF : 1;
			unsigned short SPB : 4;
			unsigned short SSLKP : 1;
			unsigned short SPIMOD : 2;
			unsigned short SPRW : 1;
			unsigned short BRDV : 2;
			unsigned short CPOL : 1;
			unsigned short CPHA : 1;
#endif
	} BIT;
	} SPCMD2;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CPHA : 1;
			unsigned short CPOL : 1;
			unsigned short BRDV : 2;
			unsigned short SPRW : 1;
			unsigned short SPIMOD : 2;
			unsigned short SSLKP : 1;
			unsigned short SPB : 4;
			unsigned short LSBF : 1;
			unsigned short SPNDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SCKDEN : 1;
#else
			unsigned short SCKDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SPNDEN : 1;
			unsigned short LSBF : 1;
			unsigned short SPB : 4;
			unsigned short SSLKP : 1;
			unsigned short SPIMOD : 2;
			unsigned short SPRW : 1;
			unsigned short BRDV : 2;
			unsigned short CPOL : 1;
			unsigned short CPHA : 1;
#endif
	} BIT;
	} SPCMD3;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char RXTRG : 3;
			unsigned char TXTRGEX : 1;
			unsigned char TXTRG : 2;
			unsigned char RXRST : 1;
			unsigned char TXRST : 1;
#else
			unsigned char TXRST : 1;
			unsigned char RXRST : 1;
			unsigned char TXTRG : 2;
			unsigned char TXTRGEX : 1;
			unsigned char RXTRG : 3;
#endif
	} BIT;
	} SPBFCR;
	char           wk1[1];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short RXBC : 6;
			unsigned short  : 2;
			unsigned short TXBC : 6;
			unsigned short  : 2;
#else
			unsigned short  : 2;
			unsigned short TXBC : 6;
			unsigned short  : 2;
			unsigned short RXBC : 6;
#endif
	} BIT;
	} SPBDCR;
	unsigned long  SPBMUL0;
	unsigned long  SPBMUL1;
	unsigned long  SPBMUL2;
	unsigned long  SPBMUL3;
} st_qspi_t;

typedef struct st_ram {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char RAMMODE : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char RAMMODE : 2;
#endif
	} BIT;
	} RAMMODE;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char RAMERR : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char RAMERR : 1;
#endif
	} BIT;
	} RAMSTS;
	char           wk0[2];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char RAMPRCR : 1;
			unsigned char KW : 7;
#else
			unsigned char KW : 7;
			unsigned char RAMPRCR : 1;
#endif
	} BIT;
	} RAMPRCR;
	char           wk1[3];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 3;
			unsigned long READ : 16;
			unsigned long  : 13;
#else
			unsigned long  : 13;
			unsigned long READ : 16;
			unsigned long  : 3;
#endif
	} BIT;
	} RAMECAD;
	char           wk2[52];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char EXRAMMODE : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char EXRAMMODE : 2;
#endif
	} BIT;
	} EXRAMMODE;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char EXRAMERR : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char EXRAMERR : 1;
#endif
	} BIT;
	} EXRAMSTS;
	char           wk3[2];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char EXRAMPRCR : 1;
			unsigned char KW : 7;
#else
			unsigned char KW : 7;
			unsigned char EXRAMPRCR : 1;
#endif
	} BIT;
	} EXRAMPRCR;
	char           wk4[3];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 3;
			unsigned long READ : 16;
			unsigned long  : 13;
#else
			unsigned long  : 13;
			unsigned long READ : 16;
			unsigned long  : 3;
#endif
	} BIT;
	} EXRAMECAD;
} st_ram_t;

typedef struct st_riic {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SDAI : 1;
			unsigned char SCLI : 1;
			unsigned char SDAO : 1;
			unsigned char SCLO : 1;
			unsigned char SOWP : 1;
			unsigned char CLO : 1;
			unsigned char IICRST : 1;
			unsigned char ICE : 1;
#else
			unsigned char ICE : 1;
			unsigned char IICRST : 1;
			unsigned char CLO : 1;
			unsigned char SOWP : 1;
			unsigned char SCLO : 1;
			unsigned char SDAO : 1;
			unsigned char SCLI : 1;
			unsigned char SDAI : 1;
#endif
	} BIT;
	} ICCR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 1;
			unsigned char ST : 1;
			unsigned char RS : 1;
			unsigned char SP : 1;
			unsigned char  : 1;
			unsigned char TRS : 1;
			unsigned char MST : 1;
			unsigned char BBSY : 1;
#else
			unsigned char BBSY : 1;
			unsigned char MST : 1;
			unsigned char TRS : 1;
			unsigned char  : 1;
			unsigned char SP : 1;
			unsigned char RS : 1;
			unsigned char ST : 1;
			unsigned char  : 1;
#endif
	} BIT;
	} ICCR2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BC : 3;
			unsigned char BCWP : 1;
			unsigned char CKS : 3;
			unsigned char MTWP : 1;
#else
			unsigned char MTWP : 1;
			unsigned char CKS : 3;
			unsigned char BCWP : 1;
			unsigned char BC : 3;
#endif
	} BIT;
	} ICMR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TMOS : 1;
			unsigned char TMOL : 1;
			unsigned char TMOH : 1;
			unsigned char  : 1;
			unsigned char SDDL : 3;
			unsigned char DLCS : 1;
#else
			unsigned char DLCS : 1;
			unsigned char SDDL : 3;
			unsigned char  : 1;
			unsigned char TMOH : 1;
			unsigned char TMOL : 1;
			unsigned char TMOS : 1;
#endif
	} BIT;
	} ICMR2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NF : 2;
			unsigned char ACKBR : 1;
			unsigned char ACKBT : 1;
			unsigned char ACKWP : 1;
			unsigned char RDRFS : 1;
			unsigned char WAIT : 1;
			unsigned char SMBS : 1;
#else
			unsigned char SMBS : 1;
			unsigned char WAIT : 1;
			unsigned char RDRFS : 1;
			unsigned char ACKWP : 1;
			unsigned char ACKBT : 1;
			unsigned char ACKBR : 1;
			unsigned char NF : 2;
#endif
	} BIT;
	} ICMR3;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TMOE : 1;
			unsigned char MALE : 1;
			unsigned char NALE : 1;
			unsigned char SALE : 1;
			unsigned char NACKE : 1;
			unsigned char NFE : 1;
			unsigned char SCLE : 1;
			unsigned char FMPE : 1;
#else
			unsigned char FMPE : 1;
			unsigned char SCLE : 1;
			unsigned char NFE : 1;
			unsigned char NACKE : 1;
			unsigned char SALE : 1;
			unsigned char NALE : 1;
			unsigned char MALE : 1;
			unsigned char TMOE : 1;
#endif
	} BIT;
	} ICFER;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SAR0E : 1;
			unsigned char SAR1E : 1;
			unsigned char SAR2E : 1;
			unsigned char GCAE : 1;
			unsigned char  : 1;
			unsigned char DIDE : 1;
			unsigned char  : 1;
			unsigned char HOAE : 1;
#else
			unsigned char HOAE : 1;
			unsigned char  : 1;
			unsigned char DIDE : 1;
			unsigned char  : 1;
			unsigned char GCAE : 1;
			unsigned char SAR2E : 1;
			unsigned char SAR1E : 1;
			unsigned char SAR0E : 1;
#endif
	} BIT;
	} ICSER;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TMOIE : 1;
			unsigned char ALIE : 1;
			unsigned char STIE : 1;
			unsigned char SPIE : 1;
			unsigned char NAKIE : 1;
			unsigned char RIE : 1;
			unsigned char TEIE : 1;
			unsigned char TIE : 1;
#else
			unsigned char TIE : 1;
			unsigned char TEIE : 1;
			unsigned char RIE : 1;
			unsigned char NAKIE : 1;
			unsigned char SPIE : 1;
			unsigned char STIE : 1;
			unsigned char ALIE : 1;
			unsigned char TMOIE : 1;
#endif
	} BIT;
	} ICIER;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char AAS0 : 1;
			unsigned char AAS1 : 1;
			unsigned char AAS2 : 1;
			unsigned char GCA : 1;
			unsigned char  : 1;
			unsigned char DID : 1;
			unsigned char  : 1;
			unsigned char HOA : 1;
#else
			unsigned char HOA : 1;
			unsigned char  : 1;
			unsigned char DID : 1;
			unsigned char  : 1;
			unsigned char GCA : 1;
			unsigned char AAS2 : 1;
			unsigned char AAS1 : 1;
			unsigned char AAS0 : 1;
#endif
	} BIT;
	} ICSR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TMOF : 1;
			unsigned char AL : 1;
			unsigned char START : 1;
			unsigned char STOP : 1;
			unsigned char NACKF : 1;
			unsigned char RDRF : 1;
			unsigned char TEND : 1;
			unsigned char TDRE : 1;
#else
			unsigned char TDRE : 1;
			unsigned char TEND : 1;
			unsigned char RDRF : 1;
			unsigned char NACKF : 1;
			unsigned char STOP : 1;
			unsigned char START : 1;
			unsigned char AL : 1;
			unsigned char TMOF : 1;
#endif
	} BIT;
	} ICSR2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SVA0 : 1;
			unsigned char SVA : 7;
#else
			unsigned char SVA : 7;
			unsigned char SVA0 : 1;
#endif
	} BIT;
	} SARL0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char FS : 1;
			unsigned char SVA : 2;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char SVA : 2;
			unsigned char FS : 1;
#endif
	} BIT;
	} SARU0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SVA0 : 1;
			unsigned char SVA : 7;
#else
			unsigned char SVA : 7;
			unsigned char SVA0 : 1;
#endif
	} BIT;
	} SARL1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char FS : 1;
			unsigned char SVA : 2;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char SVA : 2;
			unsigned char FS : 1;
#endif
	} BIT;
	} SARU1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SVA0 : 1;
			unsigned char SVA : 7;
#else
			unsigned char SVA : 7;
			unsigned char SVA0 : 1;
#endif
	} BIT;
	} SARL2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char FS : 1;
			unsigned char SVA : 2;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char SVA : 2;
			unsigned char FS : 1;
#endif
	} BIT;
	} SARU2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BRL : 5;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char BRL : 5;
#endif
	} BIT;
	} ICBRL;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BRH : 5;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char BRH : 5;
#endif
	} BIT;
	} ICBRH;
	unsigned char  ICDRT;
	unsigned char  ICDRR;
} st_riic_t;

typedef struct st_rspi {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SPMS : 1;
			unsigned char TXMD : 1;
			unsigned char MODFEN : 1;
			unsigned char MSTR : 1;
			unsigned char SPEIE : 1;
			unsigned char SPTIE : 1;
			unsigned char SPE : 1;
			unsigned char SPRIE : 1;
#else
			unsigned char SPRIE : 1;
			unsigned char SPE : 1;
			unsigned char SPTIE : 1;
			unsigned char SPEIE : 1;
			unsigned char MSTR : 1;
			unsigned char MODFEN : 1;
			unsigned char TXMD : 1;
			unsigned char SPMS : 1;
#endif
	} BIT;
	} SPCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SSL0P : 1;
			unsigned char SSL1P : 1;
			unsigned char SSL2P : 1;
			unsigned char SSL3P : 1;
			unsigned char  : 4;
#else
			unsigned char  : 4;
			unsigned char SSL3P : 1;
			unsigned char SSL2P : 1;
			unsigned char SSL1P : 1;
			unsigned char SSL0P : 1;
#endif
	} BIT;
	} SSLP;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SPLP : 1;
			unsigned char SPLP2 : 1;
			unsigned char  : 2;
			unsigned char MOIFV : 1;
			unsigned char MOIFE : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char MOIFE : 1;
			unsigned char MOIFV : 1;
			unsigned char  : 2;
			unsigned char SPLP2 : 1;
			unsigned char SPLP : 1;
#endif
	} BIT;
	} SPPCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char OVRF : 1;
			unsigned char IDLNF : 1;
			unsigned char MODF : 1;
			unsigned char PERF : 1;
			unsigned char UDRF : 1;
			unsigned char SPTEF : 1;
			unsigned char  : 1;
			unsigned char SPRF : 1;
#else
			unsigned char SPRF : 1;
			unsigned char  : 1;
			unsigned char SPTEF : 1;
			unsigned char UDRF : 1;
			unsigned char PERF : 1;
			unsigned char MODF : 1;
			unsigned char IDLNF : 1;
			unsigned char OVRF : 1;
#endif
	} BIT;
	} SPSR;
	union {
		unsigned long LONG;
		struct {
			unsigned short H;
		} WORD;
		struct {
			unsigned char HH;
		} BYTE;
	} SPDR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SPSLN : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char SPSLN : 3;
#endif
	} BIT;
	} SPSCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SPCP : 3;
			unsigned char  : 1;
			unsigned char SPECM : 3;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char SPECM : 3;
			unsigned char  : 1;
			unsigned char SPCP : 3;
#endif
	} BIT;
	} SPSSR;
	unsigned char  SPBR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SPFC : 2;
			unsigned char  : 2;
			unsigned char SPRDTD : 1;
			unsigned char SPLW : 1;
			unsigned char SPBYT : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char SPBYT : 1;
			unsigned char SPLW : 1;
			unsigned char SPRDTD : 1;
			unsigned char  : 2;
			unsigned char SPFC : 2;
#endif
	} BIT;
	} SPDCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SCKDL : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char SCKDL : 3;
#endif
	} BIT;
	} SPCKD;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SLNDL : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char SLNDL : 3;
#endif
	} BIT;
	} SSLND;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SPNDL : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char SPNDL : 3;
#endif
	} BIT;
	} SPND;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SPPE : 1;
			unsigned char SPOE : 1;
			unsigned char SPIIE : 1;
			unsigned char PTE : 1;
			unsigned char SCKASE : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char SCKASE : 1;
			unsigned char PTE : 1;
			unsigned char SPIIE : 1;
			unsigned char SPOE : 1;
			unsigned char SPPE : 1;
#endif
	} BIT;
	} SPCR2;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CPHA : 1;
			unsigned short CPOL : 1;
			unsigned short BRDV : 2;
			unsigned short SSLA : 3;
			unsigned short SSLKP : 1;
			unsigned short SPB : 4;
			unsigned short LSBF : 1;
			unsigned short SPNDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SCKDEN : 1;
#else
			unsigned short SCKDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SPNDEN : 1;
			unsigned short LSBF : 1;
			unsigned short SPB : 4;
			unsigned short SSLKP : 1;
			unsigned short SSLA : 3;
			unsigned short BRDV : 2;
			unsigned short CPOL : 1;
			unsigned short CPHA : 1;
#endif
	} BIT;
	} SPCMD0;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CPHA : 1;
			unsigned short CPOL : 1;
			unsigned short BRDV : 2;
			unsigned short SSLA : 3;
			unsigned short SSLKP : 1;
			unsigned short SPB : 4;
			unsigned short LSBF : 1;
			unsigned short SPNDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SCKDEN : 1;
#else
			unsigned short SCKDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SPNDEN : 1;
			unsigned short LSBF : 1;
			unsigned short SPB : 4;
			unsigned short SSLKP : 1;
			unsigned short SSLA : 3;
			unsigned short BRDV : 2;
			unsigned short CPOL : 1;
			unsigned short CPHA : 1;
#endif
	} BIT;
	} SPCMD1;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CPHA : 1;
			unsigned short CPOL : 1;
			unsigned short BRDV : 2;
			unsigned short SSLA : 3;
			unsigned short SSLKP : 1;
			unsigned short SPB : 4;
			unsigned short LSBF : 1;
			unsigned short SPNDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SCKDEN : 1;
#else
			unsigned short SCKDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SPNDEN : 1;
			unsigned short LSBF : 1;
			unsigned short SPB : 4;
			unsigned short SSLKP : 1;
			unsigned short SSLA : 3;
			unsigned short BRDV : 2;
			unsigned short CPOL : 1;
			unsigned short CPHA : 1;
#endif
	} BIT;
	} SPCMD2;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CPHA : 1;
			unsigned short CPOL : 1;
			unsigned short BRDV : 2;
			unsigned short SSLA : 3;
			unsigned short SSLKP : 1;
			unsigned short SPB : 4;
			unsigned short LSBF : 1;
			unsigned short SPNDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SCKDEN : 1;
#else
			unsigned short SCKDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SPNDEN : 1;
			unsigned short LSBF : 1;
			unsigned short SPB : 4;
			unsigned short SSLKP : 1;
			unsigned short SSLA : 3;
			unsigned short BRDV : 2;
			unsigned short CPOL : 1;
			unsigned short CPHA : 1;
#endif
	} BIT;
	} SPCMD3;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CPHA : 1;
			unsigned short CPOL : 1;
			unsigned short BRDV : 2;
			unsigned short SSLA : 3;
			unsigned short SSLKP : 1;
			unsigned short SPB : 4;
			unsigned short LSBF : 1;
			unsigned short SPNDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SCKDEN : 1;
#else
			unsigned short SCKDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SPNDEN : 1;
			unsigned short LSBF : 1;
			unsigned short SPB : 4;
			unsigned short SSLKP : 1;
			unsigned short SSLA : 3;
			unsigned short BRDV : 2;
			unsigned short CPOL : 1;
			unsigned short CPHA : 1;
#endif
	} BIT;
	} SPCMD4;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CPHA : 1;
			unsigned short CPOL : 1;
			unsigned short BRDV : 2;
			unsigned short SSLA : 3;
			unsigned short SSLKP : 1;
			unsigned short SPB : 4;
			unsigned short LSBF : 1;
			unsigned short SPNDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SCKDEN : 1;
#else
			unsigned short SCKDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SPNDEN : 1;
			unsigned short LSBF : 1;
			unsigned short SPB : 4;
			unsigned short SSLKP : 1;
			unsigned short SSLA : 3;
			unsigned short BRDV : 2;
			unsigned short CPOL : 1;
			unsigned short CPHA : 1;
#endif
	} BIT;
	} SPCMD5;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CPHA : 1;
			unsigned short CPOL : 1;
			unsigned short BRDV : 2;
			unsigned short SSLA : 3;
			unsigned short SSLKP : 1;
			unsigned short SPB : 4;
			unsigned short LSBF : 1;
			unsigned short SPNDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SCKDEN : 1;
#else
			unsigned short SCKDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SPNDEN : 1;
			unsigned short LSBF : 1;
			unsigned short SPB : 4;
			unsigned short SSLKP : 1;
			unsigned short SSLA : 3;
			unsigned short BRDV : 2;
			unsigned short CPOL : 1;
			unsigned short CPHA : 1;
#endif
	} BIT;
	} SPCMD6;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CPHA : 1;
			unsigned short CPOL : 1;
			unsigned short BRDV : 2;
			unsigned short SSLA : 3;
			unsigned short SSLKP : 1;
			unsigned short SPB : 4;
			unsigned short LSBF : 1;
			unsigned short SPNDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SCKDEN : 1;
#else
			unsigned short SCKDEN : 1;
			unsigned short SLNDEN : 1;
			unsigned short SPNDEN : 1;
			unsigned short LSBF : 1;
			unsigned short SPB : 4;
			unsigned short SSLKP : 1;
			unsigned short SSLA : 3;
			unsigned short BRDV : 2;
			unsigned short CPOL : 1;
			unsigned short CPHA : 1;
#endif
	} BIT;
	} SPCMD7;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BYSW : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char BYSW : 1;
#endif
	} BIT;
	} SPDCR2;
} st_rspi_t;

typedef struct st_rtc {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char F64HZ : 1;
			unsigned char F32HZ : 1;
			unsigned char F16HZ : 1;
			unsigned char F8HZ : 1;
			unsigned char F4HZ : 1;
			unsigned char F2HZ : 1;
			unsigned char F1HZ : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char F1HZ : 1;
			unsigned char F2HZ : 1;
			unsigned char F4HZ : 1;
			unsigned char F8HZ : 1;
			unsigned char F16HZ : 1;
			unsigned char F32HZ : 1;
			unsigned char F64HZ : 1;
#endif
	} BIT;
	} R64CNT;
	char           wk0[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SEC1 : 4;
			unsigned char SEC10 : 3;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char SEC10 : 3;
			unsigned char SEC1 : 4;
#endif
	} BIT;
		} RSECCNT;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCNT : 8;
#else
			unsigned char BCNT : 8;
#endif
	} BIT;
		} BCNT0;
	};
	char           wk1[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MIN1 : 4;
			unsigned char MIN10 : 3;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char MIN10 : 3;
			unsigned char MIN1 : 4;
#endif
	} BIT;
		} RMINCNT;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCNT : 8;
#else
			unsigned char BCNT : 8;
#endif
	} BIT;
		} BCNT1;
	};
	char           wk2[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char HR1 : 4;
			unsigned char HR10 : 2;
			unsigned char PM : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char PM : 1;
			unsigned char HR10 : 2;
			unsigned char HR1 : 4;
#endif
	} BIT;
		} RHRCNT;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCNT : 8;
#else
			unsigned char BCNT : 8;
#endif
	} BIT;
		} BCNT2;
	};
	char           wk3[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DAYW : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char DAYW : 3;
#endif
	} BIT;
		} RWKCNT;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCNT : 8;
#else
			unsigned char BCNT : 8;
#endif
	} BIT;
		} BCNT3;
	};
	char           wk4[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DATE1 : 4;
			unsigned char DATE10 : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char DATE10 : 2;
			unsigned char DATE1 : 4;
#endif
	} BIT;
	} RDAYCNT;
	char           wk5[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MON1 : 4;
			unsigned char MON10 : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char MON10 : 1;
			unsigned char MON1 : 4;
#endif
	} BIT;
	} RMONCNT;
	char           wk6[1];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short YR1 : 4;
			unsigned short YR10 : 4;
			unsigned short  : 8;
#else
			unsigned short  : 8;
			unsigned short YR10 : 4;
			unsigned short YR1 : 4;
#endif
	} BIT;
	} RYRCNT;
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SEC1 : 4;
			unsigned char SEC10 : 3;
			unsigned char ENB : 1;
#else
			unsigned char ENB : 1;
			unsigned char SEC10 : 3;
			unsigned char SEC1 : 4;
#endif
	} BIT;
		} RSECAR;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCNTAR : 8;
#else
			unsigned char BCNTAR : 8;
#endif
	} BIT;
		} BCNT0AR;
	};
	char           wk7[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MIN1 : 4;
			unsigned char MIN10 : 3;
			unsigned char ENB : 1;
#else
			unsigned char ENB : 1;
			unsigned char MIN10 : 3;
			unsigned char MIN1 : 4;
#endif
	} BIT;
		} RMINAR;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCNTAR : 8;
#else
			unsigned char BCNTAR : 8;
#endif
	} BIT;
		} BCNT1AR;
	};
	char           wk8[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char HR1 : 4;
			unsigned char HR10 : 2;
			unsigned char PM : 1;
			unsigned char ENB : 1;
#else
			unsigned char ENB : 1;
			unsigned char PM : 1;
			unsigned char HR10 : 2;
			unsigned char HR1 : 4;
#endif
	} BIT;
		} RHRAR;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCNTAR : 8;
#else
			unsigned char BCNTAR : 8;
#endif
	} BIT;
		} BCNT2AR;
	};
	char           wk9[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DAYW : 3;
			unsigned char  : 4;
			unsigned char ENB : 1;
#else
			unsigned char ENB : 1;
			unsigned char  : 4;
			unsigned char DAYW : 3;
#endif
	} BIT;
		} RWKAR;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCNTAR : 8;
#else
			unsigned char BCNTAR : 8;
#endif
	} BIT;
		} BCNT3AR;
	};
	char           wk10[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DATE1 : 4;
			unsigned char DATE10 : 2;
			unsigned char  : 1;
			unsigned char ENB : 1;
#else
			unsigned char ENB : 1;
			unsigned char  : 1;
			unsigned char DATE10 : 2;
			unsigned char DATE1 : 4;
#endif
	} BIT;
		} RDAYAR;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ENB : 8;
#else
			unsigned char ENB : 8;
#endif
	} BIT;
		} BCNT0AER;
	};
	char           wk11[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MON1 : 4;
			unsigned char MON10 : 1;
			unsigned char  : 2;
			unsigned char ENB : 1;
#else
			unsigned char ENB : 1;
			unsigned char  : 2;
			unsigned char MON10 : 1;
			unsigned char MON1 : 4;
#endif
	} BIT;
		} RMONAR;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ENB : 8;
#else
			unsigned char ENB : 8;
#endif
	} BIT;
		} BCNT1AER;
	};
	char           wk12[1];
	union {
		union {
			unsigned short WORD;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short YR1 : 4;
			unsigned short YR10 : 4;
			unsigned short  : 8;
#else
			unsigned short  : 8;
			unsigned short YR10 : 4;
			unsigned short YR1 : 4;
#endif
	} BIT;
		} RYRAR;
		union {
			unsigned short WORD;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ENB : 8;
			unsigned short  : 8;
#else
			unsigned short  : 8;
			unsigned short ENB : 8;
#endif
	} BIT;
		} BCNT2AER;
	};
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 7;
			unsigned char ENB : 1;
#else
			unsigned char ENB : 1;
			unsigned char  : 7;
#endif
	} BIT;
		} RYRAREN;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ENB : 8;
#else
			unsigned char ENB : 8;
#endif
	} BIT;
		} BCNT3AER;
	};
	char           wk13[3];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char AIE : 1;
			unsigned char CIE : 1;
			unsigned char PIE : 1;
			unsigned char RTCOS : 1;
			unsigned char PES : 4;
#else
			unsigned char PES : 4;
			unsigned char RTCOS : 1;
			unsigned char PIE : 1;
			unsigned char CIE : 1;
			unsigned char AIE : 1;
#endif
	} BIT;
	} RCR1;
	char           wk14[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char START : 1;
			unsigned char RESET : 1;
			unsigned char ADJ30 : 1;
			unsigned char RTCOE : 1;
			unsigned char AADJE : 1;
			unsigned char AADJP : 1;
			unsigned char HR24 : 1;
			unsigned char CNTMD : 1;
#else
			unsigned char CNTMD : 1;
			unsigned char HR24 : 1;
			unsigned char AADJP : 1;
			unsigned char AADJE : 1;
			unsigned char RTCOE : 1;
			unsigned char ADJ30 : 1;
			unsigned char RESET : 1;
			unsigned char START : 1;
#endif
	} BIT;
	} RCR2;
	char           wk15[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char RTCEN : 1;
			unsigned char RTCDV : 3;
			unsigned char  : 4;
#else
			unsigned char  : 4;
			unsigned char RTCDV : 3;
			unsigned char RTCEN : 1;
#endif
	} BIT;
	} RCR3;
	char           wk16[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char RCKSEL : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char RCKSEL : 1;
#endif
	} BIT;
	} RCR4;
	char           wk17[1];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short RFC : 1;
			unsigned short  : 15;
#else
			unsigned short  : 15;
			unsigned short RFC : 1;
#endif
	} BIT;
	} RFRH;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short RFC : 16;
#else
			unsigned short RFC : 16;
#endif
	} BIT;
	} RFRL;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ADJ : 6;
			unsigned char PMADJ : 2;
#else
			unsigned char PMADJ : 2;
			unsigned char ADJ : 6;
#endif
	} BIT;
	} RADJ;
	char           wk18[17];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TCCT : 2;
			unsigned char TCST : 1;
			unsigned char  : 1;
			unsigned char TCNF : 2;
			unsigned char  : 1;
			unsigned char TCEN : 1;
#else
			unsigned char TCEN : 1;
			unsigned char  : 1;
			unsigned char TCNF : 2;
			unsigned char  : 1;
			unsigned char TCST : 1;
			unsigned char TCCT : 2;
#endif
	} BIT;
	} RTCCR0;
	char           wk19[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TCCT : 2;
			unsigned char TCST : 1;
			unsigned char  : 1;
			unsigned char TCNF : 2;
			unsigned char  : 1;
			unsigned char TCEN : 1;
#else
			unsigned char TCEN : 1;
			unsigned char  : 1;
			unsigned char TCNF : 2;
			unsigned char  : 1;
			unsigned char TCST : 1;
			unsigned char TCCT : 2;
#endif
	} BIT;
	} RTCCR1;
	char           wk20[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TCCT : 2;
			unsigned char TCST : 1;
			unsigned char  : 1;
			unsigned char TCNF : 2;
			unsigned char  : 1;
			unsigned char TCEN : 1;
#else
			unsigned char TCEN : 1;
			unsigned char  : 1;
			unsigned char TCNF : 2;
			unsigned char  : 1;
			unsigned char TCST : 1;
			unsigned char TCCT : 2;
#endif
	} BIT;
	} RTCCR2;
	char           wk21[13];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SEC1 : 4;
			unsigned char SEC10 : 3;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char SEC10 : 3;
			unsigned char SEC1 : 4;
#endif
	} BIT;
		} RSECCP0;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCNTCP0 : 8;
#else
			unsigned char BCNTCP0 : 8;
#endif
	} BIT;
		} BCNT0CP0;
	};
	char           wk22[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MIN1 : 4;
			unsigned char MIN10 : 3;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char MIN10 : 3;
			unsigned char MIN1 : 4;
#endif
	} BIT;
		} RMINCP0;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCNTCP0 : 8;
#else
			unsigned char BCNTCP0 : 8;
#endif
	} BIT;
		} BCNT1CP0;
	};
	char           wk23[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char HR1 : 4;
			unsigned char HR10 : 2;
			unsigned char PM : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char PM : 1;
			unsigned char HR10 : 2;
			unsigned char HR1 : 4;
#endif
	} BIT;
		} RHRCP0;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCNTCP0 : 8;
#else
			unsigned char BCNTCP0 : 8;
#endif
	} BIT;
		} BCNT2CP0;
	};
	char           wk24[3];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DATE1 : 4;
			unsigned char DATE10 : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char DATE10 : 2;
			unsigned char DATE1 : 4;
#endif
	} BIT;
		} RDAYCP0;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCNTCP0 : 8;
#else
			unsigned char BCNTCP0 : 8;
#endif
	} BIT;
		} BCNT3CP0;
	};
	char           wk25[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MON1 : 4;
			unsigned char MON10 : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char MON10 : 1;
			unsigned char MON1 : 4;
#endif
	} BIT;
	} RMONCP0;
	char           wk26[5];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SEC1 : 4;
			unsigned char SEC10 : 3;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char SEC10 : 3;
			unsigned char SEC1 : 4;
#endif
	} BIT;
		} RSECCP1;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCNTCP1 : 8;
#else
			unsigned char BCNTCP1 : 8;
#endif
	} BIT;
		} BCNT0CP1;
	};
	char           wk27[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MIN1 : 4;
			unsigned char MIN10 : 3;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char MIN10 : 3;
			unsigned char MIN1 : 4;
#endif
	} BIT;
		} RMINCP1;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCNTCP1 : 8;
#else
			unsigned char BCNTCP1 : 8;
#endif
	} BIT;
		} BCNT1CP1;
	};
	char           wk28[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char HR1 : 4;
			unsigned char HR10 : 2;
			unsigned char PM : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char PM : 1;
			unsigned char HR10 : 2;
			unsigned char HR1 : 4;
#endif
	} BIT;
		} RHRCP1;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCNTCP1 : 8;
#else
			unsigned char BCNTCP1 : 8;
#endif
	} BIT;
		} BCNT2CP1;
	};
	char           wk29[3];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DATE1 : 4;
			unsigned char DATE10 : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char DATE10 : 2;
			unsigned char DATE1 : 4;
#endif
	} BIT;
		} RDAYCP1;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCNTCP1 : 8;
#else
			unsigned char BCNTCP1 : 8;
#endif
	} BIT;
		} BCNT3CP1;
	};
	char           wk30[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MON1 : 4;
			unsigned char MON10 : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char MON10 : 1;
			unsigned char MON1 : 4;
#endif
	} BIT;
	} RMONCP1;
	char           wk31[5];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SEC1 : 4;
			unsigned char SEC10 : 3;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char SEC10 : 3;
			unsigned char SEC1 : 4;
#endif
	} BIT;
		} RSECCP2;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCNTCP2 : 8;
#else
			unsigned char BCNTCP2 : 8;
#endif
	} BIT;
		} BCNT0CP2;
	};
	char           wk32[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MIN1 : 4;
			unsigned char MIN10 : 3;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char MIN10 : 3;
			unsigned char MIN1 : 4;
#endif
	} BIT;
		} RMINCP2;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCNTCP2 : 8;
#else
			unsigned char BCNTCP2 : 8;
#endif
	} BIT;
		} BCNT1CP2;
	};
	char           wk33[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char HR1 : 4;
			unsigned char HR10 : 2;
			unsigned char PM : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char PM : 1;
			unsigned char HR10 : 2;
			unsigned char HR1 : 4;
#endif
	} BIT;
		} RHRCP2;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCNTCP2 : 8;
#else
			unsigned char BCNTCP2 : 8;
#endif
	} BIT;
		} BCNT2CP2;
	};
	char           wk34[3];
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DATE1 : 4;
			unsigned char DATE10 : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char DATE10 : 2;
			unsigned char DATE1 : 4;
#endif
	} BIT;
		} RDAYCP2;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCNTCP2 : 8;
#else
			unsigned char BCNTCP2 : 8;
#endif
	} BIT;
		} BCNT3CP2;
	};
	char           wk35[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MON1 : 4;
			unsigned char MON10 : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char MON10 : 1;
			unsigned char MON1 : 4;
#endif
	} BIT;
	} RMONCP2;
} st_rtc_t;

typedef struct st_s12ad {
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short DBLANS : 5;
			unsigned short  : 1;
			unsigned short GBADIE : 1;
			unsigned short DBLE : 1;
			unsigned short EXTRG : 1;
			unsigned short TRGE : 1;
			unsigned short  : 2;
			unsigned short ADIE : 1;
			unsigned short ADCS : 2;
			unsigned short ADST : 1;
#else
			unsigned short ADST : 1;
			unsigned short ADCS : 2;
			unsigned short ADIE : 1;
			unsigned short  : 2;
			unsigned short TRGE : 1;
			unsigned short EXTRG : 1;
			unsigned short DBLE : 1;
			unsigned short GBADIE : 1;
			unsigned short  : 1;
			unsigned short DBLANS : 5;
#endif
	} BIT;
	} ADCSR;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ANSA000 : 1;
			unsigned short ANSA001 : 1;
			unsigned short ANSA002 : 1;
			unsigned short ANSA003 : 1;
			unsigned short ANSA004 : 1;
			unsigned short ANSA005 : 1;
			unsigned short ANSA006 : 1;
			unsigned short ANSA007 : 1;
			unsigned short  : 8;
#else
			unsigned short  : 8;
			unsigned short ANSA007 : 1;
			unsigned short ANSA006 : 1;
			unsigned short ANSA005 : 1;
			unsigned short ANSA004 : 1;
			unsigned short ANSA003 : 1;
			unsigned short ANSA002 : 1;
			unsigned short ANSA001 : 1;
			unsigned short ANSA000 : 1;
#endif
	} BIT;
	} ADANSA0;
	char           wk1[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ADS000 : 1;
			unsigned short ADS001 : 1;
			unsigned short ADS002 : 1;
			unsigned short ADS003 : 1;
			unsigned short ADS004 : 1;
			unsigned short ADS005 : 1;
			unsigned short ADS006 : 1;
			unsigned short ADS007 : 1;
			unsigned short  : 8;
#else
			unsigned short  : 8;
			unsigned short ADS007 : 1;
			unsigned short ADS006 : 1;
			unsigned short ADS005 : 1;
			unsigned short ADS004 : 1;
			unsigned short ADS003 : 1;
			unsigned short ADS002 : 1;
			unsigned short ADS001 : 1;
			unsigned short ADS000 : 1;
#endif
	} BIT;
	} ADADS0;
	char           wk2[2];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ADC : 3;
			unsigned char  : 4;
			unsigned char AVEE : 1;
#else
			unsigned char AVEE : 1;
			unsigned char  : 4;
			unsigned char ADC : 3;
#endif
	} BIT;
	} ADADC;
	char           wk3[1];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 1;
			unsigned short ADPRC : 2;
			unsigned short  : 2;
			unsigned short ACE : 1;
			unsigned short  : 2;
			unsigned short DIAGVAL : 2;
			unsigned short DIAGLD : 1;
			unsigned short DIAGM : 1;
			unsigned short  : 3;
			unsigned short ADRFMT : 1;
#else
			unsigned short ADRFMT : 1;
			unsigned short  : 3;
			unsigned short DIAGM : 1;
			unsigned short DIAGLD : 1;
			unsigned short DIAGVAL : 2;
			unsigned short  : 2;
			unsigned short ACE : 1;
			unsigned short  : 2;
			unsigned short ADPRC : 2;
			unsigned short  : 1;
#endif
	} BIT;
	} ADCER;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short TRSB : 6;
			unsigned short  : 2;
			unsigned short TRSA : 6;
			unsigned short  : 2;
#else
			unsigned short  : 2;
			unsigned short TRSA : 6;
			unsigned short  : 2;
			unsigned short TRSB : 6;
#endif
	} BIT;
	} ADSTRGR;
	char           wk4[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ANSB000 : 1;
			unsigned short ANSB001 : 1;
			unsigned short ANSB002 : 1;
			unsigned short ANSB003 : 1;
			unsigned short ANSB004 : 1;
			unsigned short ANSB005 : 1;
			unsigned short ANSB006 : 1;
			unsigned short ANSB007 : 1;
			unsigned short  : 8;
#else
			unsigned short  : 8;
			unsigned short ANSB007 : 1;
			unsigned short ANSB006 : 1;
			unsigned short ANSB005 : 1;
			unsigned short ANSB004 : 1;
			unsigned short ANSB003 : 1;
			unsigned short ANSB002 : 1;
			unsigned short ANSB001 : 1;
			unsigned short ANSB000 : 1;
#endif
	} BIT;
	} ADANSB0;
	char           wk5[2];
	union {
		unsigned short WORD;
	} ADDBLDR;
	char           wk6[4];
	union {
		unsigned short WORD;
		union {
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short AD : 12;
			unsigned short  : 2;
			unsigned short DIAGST : 2;
#else
			unsigned short DIAGST : 2;
			unsigned short  : 2;
			unsigned short AD : 12;
#endif
	} RIGHT;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short DIAGST : 2;
			unsigned short  : 2;
			unsigned short AD : 12;
#else
			unsigned short AD : 12;
			unsigned short  : 2;
			unsigned short DIAGST : 2;
#endif
	} LEFT;
		} BIT;
	} ADRD;
	unsigned short ADDR0;
	unsigned short ADDR1;
	unsigned short ADDR2;
	unsigned short ADDR3;
	unsigned short ADDR4;
	unsigned short ADDR5;
	unsigned short ADDR6;
	unsigned short ADDR7;
	char           wk7[51];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PRO : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char PRO : 2;
#endif
	} BIT;
	} ADSAMPR;
	char           wk8[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short SSTSH : 8;
			unsigned short SHANS : 3;
			unsigned short  : 5;
#else
			unsigned short  : 5;
			unsigned short SHANS : 3;
			unsigned short SSTSH : 8;
#endif
	} BIT;
	} ADSHCR;
	char           wk9[6];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 5;
			unsigned short SAM : 1;
			unsigned short  : 10;
#else
			unsigned short  : 10;
			unsigned short SAM : 1;
			unsigned short  : 5;
#endif
	} BIT;
	} ADSAM;
	char           wk10[10];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ADNDIS : 5;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char ADNDIS : 5;
#endif
	} BIT;
	} ADDISCR;
	char           wk11[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SHMD : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char SHMD : 1;
#endif
	} BIT;
	} ADSHMSR;
	char           wk12[3];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PGS : 1;
			unsigned short GBRSCN : 1;
			unsigned short  : 12;
			unsigned short LGRRS : 1;
			unsigned short GBRP : 1;
#else
			unsigned short GBRP : 1;
			unsigned short LGRRS : 1;
			unsigned short  : 12;
			unsigned short GBRSCN : 1;
			unsigned short PGS : 1;
#endif
	} BIT;
	} ADGSPCR;
	char           wk13[2];
	unsigned short ADDBLDRA;
	unsigned short ADDBLDRB;
	char           wk14[4];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MONCOMB : 1;
			unsigned char  : 3;
			unsigned char MONCMPA : 1;
			unsigned char MONCMPB : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char MONCMPB : 1;
			unsigned char MONCMPA : 1;
			unsigned char  : 3;
			unsigned char MONCOMB : 1;
#endif
	} BIT;
	} ADWINMON;
	char           wk15[3];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CMPAB : 2;
			unsigned short  : 7;
			unsigned short CMPBE : 1;
			unsigned short  : 1;
			unsigned short CMPAE : 1;
			unsigned short  : 1;
			unsigned short CMPBIE : 1;
			unsigned short WCMPE : 1;
			unsigned short CMPAIE : 1;
#else
			unsigned short CMPAIE : 1;
			unsigned short WCMPE : 1;
			unsigned short CMPBIE : 1;
			unsigned short  : 1;
			unsigned short CMPAE : 1;
			unsigned short  : 1;
			unsigned short CMPBE : 1;
			unsigned short  : 7;
			unsigned short CMPAB : 2;
#endif
	} BIT;
	} ADCMPCR;
	char           wk16[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CMPCHA000 : 1;
			unsigned short CMPCHA001 : 1;
			unsigned short CMPCHA002 : 1;
			unsigned short CMPCHA003 : 1;
			unsigned short CMPCHA004 : 1;
			unsigned short CMPCHA005 : 1;
			unsigned short CMPCHA006 : 1;
			unsigned short CMPCHA007 : 1;
			unsigned short  : 8;
#else
			unsigned short  : 8;
			unsigned short CMPCHA007 : 1;
			unsigned short CMPCHA006 : 1;
			unsigned short CMPCHA005 : 1;
			unsigned short CMPCHA004 : 1;
			unsigned short CMPCHA003 : 1;
			unsigned short CMPCHA002 : 1;
			unsigned short CMPCHA001 : 1;
			unsigned short CMPCHA000 : 1;
#endif
	} BIT;
	} ADCMPANSR0;
	char           wk17[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CMPLCHA000 : 1;
			unsigned short CMPLCHA001 : 1;
			unsigned short CMPLCHA002 : 1;
			unsigned short CMPLCHA003 : 1;
			unsigned short CMPLCHA004 : 1;
			unsigned short CMPLCHA005 : 1;
			unsigned short CMPLCHA006 : 1;
			unsigned short CMPLCHA007 : 1;
			unsigned short  : 8;
#else
			unsigned short  : 8;
			unsigned short CMPLCHA007 : 1;
			unsigned short CMPLCHA006 : 1;
			unsigned short CMPLCHA005 : 1;
			unsigned short CMPLCHA004 : 1;
			unsigned short CMPLCHA003 : 1;
			unsigned short CMPLCHA002 : 1;
			unsigned short CMPLCHA001 : 1;
			unsigned short CMPLCHA000 : 1;
#endif
	} BIT;
	} ADCMPLR0;
	char           wk18[2];
	unsigned short ADCMPDR0;
	unsigned short ADCMPDR1;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CMPSTCHA000 : 1;
			unsigned short CMPSTCHA001 : 1;
			unsigned short CMPSTCHA002 : 1;
			unsigned short CMPSTCHA003 : 1;
			unsigned short CMPSTCHA004 : 1;
			unsigned short CMPSTCHA005 : 1;
			unsigned short CMPSTCHA006 : 1;
			unsigned short CMPSTCHA007 : 1;
			unsigned short  : 8;
#else
			unsigned short  : 8;
			unsigned short CMPSTCHA007 : 1;
			unsigned short CMPSTCHA006 : 1;
			unsigned short CMPSTCHA005 : 1;
			unsigned short CMPSTCHA004 : 1;
			unsigned short CMPSTCHA003 : 1;
			unsigned short CMPSTCHA002 : 1;
			unsigned short CMPSTCHA001 : 1;
			unsigned short CMPSTCHA000 : 1;
#endif
	} BIT;
	} ADCMPSR0;
	char           wk19[4];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CMPCHB : 6;
			unsigned char  : 1;
			unsigned char CMPLB : 1;
#else
			unsigned char CMPLB : 1;
			unsigned char  : 1;
			unsigned char CMPCHB : 6;
#endif
	} BIT;
	} ADCMPBNSR;
	char           wk20[1];
	unsigned short ADWINLLB;
	unsigned short ADWINULB;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CMPSTB : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char CMPSTB : 1;
#endif
	} BIT;
	} ADCMPBSR;
	char           wk21[39];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ANSC000 : 1;
			unsigned short ANSC001 : 1;
			unsigned short ANSC002 : 1;
			unsigned short ANSC003 : 1;
			unsigned short ANSC004 : 1;
			unsigned short ANSC005 : 1;
			unsigned short ANSC006 : 1;
			unsigned short ANSC007 : 1;
			unsigned short  : 8;
#else
			unsigned short  : 8;
			unsigned short ANSC007 : 1;
			unsigned short ANSC006 : 1;
			unsigned short ANSC005 : 1;
			unsigned short ANSC004 : 1;
			unsigned short ANSC003 : 1;
			unsigned short ANSC002 : 1;
			unsigned short ANSC001 : 1;
			unsigned short ANSC000 : 1;
#endif
	} BIT;
	} ADANSC0;
	char           wk22[3];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TRSC : 6;
			unsigned char GCADIE : 1;
			unsigned char GRCE : 1;
#else
			unsigned char GRCE : 1;
			unsigned char GCADIE : 1;
			unsigned char TRSC : 6;
#endif
	} BIT;
	} ADGCTRGR;
	char           wk23[6];
	unsigned char  ADSSTR0;
	unsigned char  ADSSTR1;
	unsigned char  ADSSTR2;
	unsigned char  ADSSTR3;
	unsigned char  ADSSTR4;
	unsigned char  ADSSTR5;
	unsigned char  ADSSTR6;
	unsigned char  ADSSTR7;
} st_s12ad_t;

typedef struct st_s12ad1 {
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short DBLANS : 5;
			unsigned short  : 1;
			unsigned short GBADIE : 1;
			unsigned short DBLE : 1;
			unsigned short EXTRG : 1;
			unsigned short TRGE : 1;
			unsigned short  : 2;
			unsigned short ADIE : 1;
			unsigned short ADCS : 2;
			unsigned short ADST : 1;
#else
			unsigned short ADST : 1;
			unsigned short ADCS : 2;
			unsigned short ADIE : 1;
			unsigned short  : 2;
			unsigned short TRGE : 1;
			unsigned short EXTRG : 1;
			unsigned short DBLE : 1;
			unsigned short GBADIE : 1;
			unsigned short  : 1;
			unsigned short DBLANS : 5;
#endif
	} BIT;
	} ADCSR;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ANSA000 : 1;
			unsigned short ANSA001 : 1;
			unsigned short ANSA002 : 1;
			unsigned short ANSA003 : 1;
			unsigned short ANSA004 : 1;
			unsigned short ANSA005 : 1;
			unsigned short ANSA006 : 1;
			unsigned short ANSA007 : 1;
			unsigned short ANSA008 : 1;
			unsigned short ANSA009 : 1;
			unsigned short ANSA010 : 1;
			unsigned short ANSA011 : 1;
			unsigned short ANSA012 : 1;
			unsigned short ANSA013 : 1;
			unsigned short ANSA014 : 1;
			unsigned short ANSA015 : 1;
#else
			unsigned short ANSA015 : 1;
			unsigned short ANSA014 : 1;
			unsigned short ANSA013 : 1;
			unsigned short ANSA012 : 1;
			unsigned short ANSA011 : 1;
			unsigned short ANSA010 : 1;
			unsigned short ANSA009 : 1;
			unsigned short ANSA008 : 1;
			unsigned short ANSA007 : 1;
			unsigned short ANSA006 : 1;
			unsigned short ANSA005 : 1;
			unsigned short ANSA004 : 1;
			unsigned short ANSA003 : 1;
			unsigned short ANSA002 : 1;
			unsigned short ANSA001 : 1;
			unsigned short ANSA000 : 1;
#endif
	} BIT;
	} ADANSA0;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ANSA100 : 1;
			unsigned short ANSA101 : 1;
			unsigned short ANSA102 : 1;
			unsigned short ANSA103 : 1;
			unsigned short ANSA104 : 1;
			unsigned short  : 11;
#else
			unsigned short  : 11;
			unsigned short ANSA104 : 1;
			unsigned short ANSA103 : 1;
			unsigned short ANSA102 : 1;
			unsigned short ANSA101 : 1;
			unsigned short ANSA100 : 1;
#endif
	} BIT;
	} ADANSA1;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ADS000 : 1;
			unsigned short ADS001 : 1;
			unsigned short ADS002 : 1;
			unsigned short ADS003 : 1;
			unsigned short ADS004 : 1;
			unsigned short ADS005 : 1;
			unsigned short ADS006 : 1;
			unsigned short ADS007 : 1;
			unsigned short ADS008 : 1;
			unsigned short ADS009 : 1;
			unsigned short ADS010 : 1;
			unsigned short ADS011 : 1;
			unsigned short ADS012 : 1;
			unsigned short ADS013 : 1;
			unsigned short ADS014 : 1;
			unsigned short ADS015 : 1;
#else
			unsigned short ADS015 : 1;
			unsigned short ADS014 : 1;
			unsigned short ADS013 : 1;
			unsigned short ADS012 : 1;
			unsigned short ADS011 : 1;
			unsigned short ADS010 : 1;
			unsigned short ADS009 : 1;
			unsigned short ADS008 : 1;
			unsigned short ADS007 : 1;
			unsigned short ADS006 : 1;
			unsigned short ADS005 : 1;
			unsigned short ADS004 : 1;
			unsigned short ADS003 : 1;
			unsigned short ADS002 : 1;
			unsigned short ADS001 : 1;
			unsigned short ADS000 : 1;
#endif
	} BIT;
	} ADADS0;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ADS100 : 1;
			unsigned short ADS101 : 1;
			unsigned short ADS102 : 1;
			unsigned short ADS103 : 1;
			unsigned short ADS104 : 1;
			unsigned short  : 11;
#else
			unsigned short  : 11;
			unsigned short ADS104 : 1;
			unsigned short ADS103 : 1;
			unsigned short ADS102 : 1;
			unsigned short ADS101 : 1;
			unsigned short ADS100 : 1;
#endif
	} BIT;
	} ADADS1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ADC : 3;
			unsigned char  : 4;
			unsigned char AVEE : 1;
#else
			unsigned char AVEE : 1;
			unsigned char  : 4;
			unsigned char ADC : 3;
#endif
	} BIT;
	} ADADC;
	char           wk1[1];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 1;
			unsigned short ADPRC : 2;
			unsigned short  : 2;
			unsigned short ACE : 1;
			unsigned short  : 2;
			unsigned short DIAGVAL : 2;
			unsigned short DIAGLD : 1;
			unsigned short DIAGM : 1;
			unsigned short  : 3;
			unsigned short ADRFMT : 1;
#else
			unsigned short ADRFMT : 1;
			unsigned short  : 3;
			unsigned short DIAGM : 1;
			unsigned short DIAGLD : 1;
			unsigned short DIAGVAL : 2;
			unsigned short  : 2;
			unsigned short ACE : 1;
			unsigned short  : 2;
			unsigned short ADPRC : 2;
			unsigned short  : 1;
#endif
	} BIT;
	} ADCER;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short TRSB : 6;
			unsigned short  : 2;
			unsigned short TRSA : 6;
			unsigned short  : 2;
#else
			unsigned short  : 2;
			unsigned short TRSA : 6;
			unsigned short  : 2;
			unsigned short TRSB : 6;
#endif
	} BIT;
	} ADSTRGR;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short TSSAD : 1;
			unsigned short OCSAD : 1;
			unsigned short  : 6;
			unsigned short TSSA : 1;
			unsigned short OCSA : 1;
			unsigned short TSSB : 1;
			unsigned short OCSB : 1;
			unsigned short  : 1;
			unsigned short EXSEL : 2;
			unsigned short EXOEN : 1;
#else
			unsigned short EXOEN : 1;
			unsigned short EXSEL : 2;
			unsigned short  : 1;
			unsigned short OCSB : 1;
			unsigned short TSSB : 1;
			unsigned short OCSA : 1;
			unsigned short TSSA : 1;
			unsigned short  : 6;
			unsigned short OCSAD : 1;
			unsigned short TSSAD : 1;
#endif
	} BIT;
	} ADEXICR;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ANSB000 : 1;
			unsigned short ANSB001 : 1;
			unsigned short ANSB002 : 1;
			unsigned short ANSB003 : 1;
			unsigned short ANSB004 : 1;
			unsigned short ANSB005 : 1;
			unsigned short ANSB006 : 1;
			unsigned short ANSB007 : 1;
			unsigned short ANSB008 : 1;
			unsigned short ANSB009 : 1;
			unsigned short ANSB010 : 1;
			unsigned short ANSB011 : 1;
			unsigned short ANSB012 : 1;
			unsigned short ANSB013 : 1;
			unsigned short ANSB014 : 1;
			unsigned short ANSB015 : 1;
#else
			unsigned short ANSB015 : 1;
			unsigned short ANSB014 : 1;
			unsigned short ANSB013 : 1;
			unsigned short ANSB012 : 1;
			unsigned short ANSB011 : 1;
			unsigned short ANSB010 : 1;
			unsigned short ANSB009 : 1;
			unsigned short ANSB008 : 1;
			unsigned short ANSB007 : 1;
			unsigned short ANSB006 : 1;
			unsigned short ANSB005 : 1;
			unsigned short ANSB004 : 1;
			unsigned short ANSB003 : 1;
			unsigned short ANSB002 : 1;
			unsigned short ANSB001 : 1;
			unsigned short ANSB000 : 1;
#endif
	} BIT;
	} ADANSB0;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ANSB100 : 1;
			unsigned short ANSB101 : 1;
			unsigned short ANSB102 : 1;
			unsigned short ANSB103 : 1;
			unsigned short ANSB104 : 1;
			unsigned short  : 11;
#else
			unsigned short  : 11;
			unsigned short ANSB104 : 1;
			unsigned short ANSB103 : 1;
			unsigned short ANSB102 : 1;
			unsigned short ANSB101 : 1;
			unsigned short ANSB100 : 1;
#endif
	} BIT;
	} ADANSB1;
	unsigned short ADDBLDR;
	unsigned short ADTSDR;
	unsigned short ADOCDR;
	union {
		unsigned short WORD;
		union {
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short AD : 12;
			unsigned short  : 2;
			unsigned short DIAGST : 2;
#else
			unsigned short DIAGST : 2;
			unsigned short  : 2;
			unsigned short AD : 12;
#endif
	} RIGHT;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short DIAGST : 2;
			unsigned short  : 2;
			unsigned short AD : 12;
#else
			unsigned short AD : 12;
			unsigned short  : 2;
			unsigned short DIAGST : 2;
#endif
	} LEFT;
		} BIT;
	} ADRD;
	unsigned short ADDR0;
	unsigned short ADDR1;
	unsigned short ADDR2;
	unsigned short ADDR3;
	unsigned short ADDR4;
	unsigned short ADDR5;
	unsigned short ADDR6;
	unsigned short ADDR7;
	unsigned short ADDR8;
	unsigned short ADDR9;
	unsigned short ADDR10;
	unsigned short ADDR11;
	unsigned short ADDR12;
	unsigned short ADDR13;
	unsigned short ADDR14;
	unsigned short ADDR15;
	unsigned short ADDR16;
	unsigned short ADDR17;
	unsigned short ADDR18;
	unsigned short ADDR19;
	unsigned short ADDR20;
	char           wk2[25];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PRO : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char PRO : 2;
#endif
	} BIT;
	} ADSAMPR;
	char           wk3[10];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 5;
			unsigned short SAM : 1;
			unsigned short  : 10;
#else
			unsigned short  : 10;
			unsigned short SAM : 1;
			unsigned short  : 5;
#endif
	} BIT;
	} ADSAM;
	char           wk4[10];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ADNDIS : 5;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char ADNDIS : 5;
#endif
	} BIT;
	} ADDISCR;
	char           wk5[5];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PGS : 1;
			unsigned short GBRSCN : 1;
			unsigned short  : 12;
			unsigned short LGRRS : 1;
			unsigned short GBRP : 1;
#else
			unsigned short GBRP : 1;
			unsigned short LGRRS : 1;
			unsigned short  : 12;
			unsigned short GBRSCN : 1;
			unsigned short PGS : 1;
#endif
	} BIT;
	} ADGSPCR;
	char           wk6[2];
	unsigned short ADDBLDRA;
	unsigned short ADDBLDRB;
	char           wk7[4];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MONCOMB : 1;
			unsigned char  : 3;
			unsigned char MONCMPA : 1;
			unsigned char MONCMPB : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char MONCMPB : 1;
			unsigned char MONCMPA : 1;
			unsigned char  : 3;
			unsigned char MONCOMB : 1;
#endif
	} BIT;
	} ADWINMON;
	char           wk8[3];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CMPAB : 2;
			unsigned short  : 7;
			unsigned short CMPBE : 1;
			unsigned short  : 1;
			unsigned short CMPAE : 1;
			unsigned short  : 1;
			unsigned short CMPBIE : 1;
			unsigned short WCMPE : 1;
			unsigned short CMPAIE : 1;
#else
			unsigned short CMPAIE : 1;
			unsigned short WCMPE : 1;
			unsigned short CMPBIE : 1;
			unsigned short  : 1;
			unsigned short CMPAE : 1;
			unsigned short  : 1;
			unsigned short CMPBE : 1;
			unsigned short  : 7;
			unsigned short CMPAB : 2;
#endif
	} BIT;
	} ADCMPCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CMPSTS : 1;
			unsigned char CMPSOC : 1;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char CMPSOC : 1;
			unsigned char CMPSTS : 1;
#endif
	} BIT;
	} ADCMPANSER;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CMPLTS : 1;
			unsigned char CMPLOC : 1;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char CMPLOC : 1;
			unsigned char CMPLTS : 1;
#endif
	} BIT;
	} ADCMPLER;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CMPCHA000 : 1;
			unsigned short CMPCHA001 : 1;
			unsigned short CMPCHA002 : 1;
			unsigned short CMPCHA003 : 1;
			unsigned short CMPCHA004 : 1;
			unsigned short CMPCHA005 : 1;
			unsigned short CMPCHA006 : 1;
			unsigned short CMPCHA007 : 1;
			unsigned short CMPCHA008 : 1;
			unsigned short CMPCHA009 : 1;
			unsigned short CMPCHA010 : 1;
			unsigned short CMPCHA011 : 1;
			unsigned short CMPCHA012 : 1;
			unsigned short CMPCHA013 : 1;
			unsigned short CMPCHA014 : 1;
			unsigned short CMPCHA015 : 1;
#else
			unsigned short CMPCHA015 : 1;
			unsigned short CMPCHA014 : 1;
			unsigned short CMPCHA013 : 1;
			unsigned short CMPCHA012 : 1;
			unsigned short CMPCHA011 : 1;
			unsigned short CMPCHA010 : 1;
			unsigned short CMPCHA009 : 1;
			unsigned short CMPCHA008 : 1;
			unsigned short CMPCHA007 : 1;
			unsigned short CMPCHA006 : 1;
			unsigned short CMPCHA005 : 1;
			unsigned short CMPCHA004 : 1;
			unsigned short CMPCHA003 : 1;
			unsigned short CMPCHA002 : 1;
			unsigned short CMPCHA001 : 1;
			unsigned short CMPCHA000 : 1;
#endif
	} BIT;
	} ADCMPANSR0;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CMPCHA100 : 1;
			unsigned short CMPCHA101 : 1;
			unsigned short CMPCHA102 : 1;
			unsigned short CMPCHA103 : 1;
			unsigned short CMPCHA104 : 1;
			unsigned short  : 11;
#else
			unsigned short  : 11;
			unsigned short CMPCHA104 : 1;
			unsigned short CMPCHA103 : 1;
			unsigned short CMPCHA102 : 1;
			unsigned short CMPCHA101 : 1;
			unsigned short CMPCHA100 : 1;
#endif
	} BIT;
	} ADCMPANSR1;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CMPLCHA000 : 1;
			unsigned short CMPLCHA001 : 1;
			unsigned short CMPLCHA002 : 1;
			unsigned short CMPLCHA003 : 1;
			unsigned short CMPLCHA004 : 1;
			unsigned short CMPLCHA005 : 1;
			unsigned short CMPLCHA006 : 1;
			unsigned short CMPLCHA007 : 1;
			unsigned short CMPLCHA008 : 1;
			unsigned short CMPLCHA009 : 1;
			unsigned short CMPLCHA010 : 1;
			unsigned short CMPLCHA011 : 1;
			unsigned short CMPLCHA012 : 1;
			unsigned short CMPLCHA013 : 1;
			unsigned short CMPLCHA014 : 1;
			unsigned short CMPLCHA015 : 1;
#else
			unsigned short CMPLCHA015 : 1;
			unsigned short CMPLCHA014 : 1;
			unsigned short CMPLCHA013 : 1;
			unsigned short CMPLCHA012 : 1;
			unsigned short CMPLCHA011 : 1;
			unsigned short CMPLCHA010 : 1;
			unsigned short CMPLCHA009 : 1;
			unsigned short CMPLCHA008 : 1;
			unsigned short CMPLCHA007 : 1;
			unsigned short CMPLCHA006 : 1;
			unsigned short CMPLCHA005 : 1;
			unsigned short CMPLCHA004 : 1;
			unsigned short CMPLCHA003 : 1;
			unsigned short CMPLCHA002 : 1;
			unsigned short CMPLCHA001 : 1;
			unsigned short CMPLCHA000 : 1;
#endif
	} BIT;
	} ADCMPLR0;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CMPLCHA100 : 1;
			unsigned short CMPLCHA101 : 1;
			unsigned short CMPLCHA102 : 1;
			unsigned short CMPLCHA103 : 1;
			unsigned short CMPLCHA104 : 1;
			unsigned short  : 11;
#else
			unsigned short  : 11;
			unsigned short CMPLCHA104 : 1;
			unsigned short CMPLCHA103 : 1;
			unsigned short CMPLCHA102 : 1;
			unsigned short CMPLCHA101 : 1;
			unsigned short CMPLCHA100 : 1;
#endif
	} BIT;
	} ADCMPLR1;
	unsigned short ADCMPDR0;
	unsigned short ADCMPDR1;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CMPSTCHA000 : 1;
			unsigned short CMPSTCHA001 : 1;
			unsigned short CMPSTCHA002 : 1;
			unsigned short CMPSTCHA003 : 1;
			unsigned short CMPSTCHA004 : 1;
			unsigned short CMPSTCHA005 : 1;
			unsigned short CMPSTCHA006 : 1;
			unsigned short CMPSTCHA007 : 1;
			unsigned short CMPSTCHA008 : 1;
			unsigned short CMPSTCHA009 : 1;
			unsigned short CMPSTCHA010 : 1;
			unsigned short CMPSTCHA011 : 1;
			unsigned short CMPSTCHA012 : 1;
			unsigned short CMPSTCHA013 : 1;
			unsigned short CMPSTCHA014 : 1;
			unsigned short CMPSTCHA015 : 1;
#else
			unsigned short CMPSTCHA015 : 1;
			unsigned short CMPSTCHA014 : 1;
			unsigned short CMPSTCHA013 : 1;
			unsigned short CMPSTCHA012 : 1;
			unsigned short CMPSTCHA011 : 1;
			unsigned short CMPSTCHA010 : 1;
			unsigned short CMPSTCHA009 : 1;
			unsigned short CMPSTCHA008 : 1;
			unsigned short CMPSTCHA007 : 1;
			unsigned short CMPSTCHA006 : 1;
			unsigned short CMPSTCHA005 : 1;
			unsigned short CMPSTCHA004 : 1;
			unsigned short CMPSTCHA003 : 1;
			unsigned short CMPSTCHA002 : 1;
			unsigned short CMPSTCHA001 : 1;
			unsigned short CMPSTCHA000 : 1;
#endif
	} BIT;
	} ADCMPSR0;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CMPSTCHA100 : 1;
			unsigned short CMPSTCHA101 : 1;
			unsigned short CMPSTCHA102 : 1;
			unsigned short CMPSTCHA103 : 1;
			unsigned short CMPSTCHA104 : 1;
			unsigned short  : 11;
#else
			unsigned short  : 11;
			unsigned short CMPSTCHA104 : 1;
			unsigned short CMPSTCHA103 : 1;
			unsigned short CMPSTCHA102 : 1;
			unsigned short CMPSTCHA101 : 1;
			unsigned short CMPSTCHA100 : 1;
#endif
	} BIT;
	} ADCMPSR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CMPFTS : 1;
			unsigned char CMPFOC : 1;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char CMPFOC : 1;
			unsigned char CMPFTS : 1;
#endif
	} BIT;
	} ADCMPSER;
	char           wk9[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CMPCHB : 6;
			unsigned char  : 1;
			unsigned char CMPLB : 1;
#else
			unsigned char CMPLB : 1;
			unsigned char  : 1;
			unsigned char CMPCHB : 6;
#endif
	} BIT;
	} ADCMPBNSR;
	char           wk10[1];
	unsigned short ADWINLLB;
	unsigned short ADWINULB;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CMPSTB : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char CMPSTB : 1;
#endif
	} BIT;
	} ADCMPBSR;
	char           wk11[39];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ANSC000 : 1;
			unsigned short ANSC001 : 1;
			unsigned short ANSC002 : 1;
			unsigned short ANSC003 : 1;
			unsigned short ANSC004 : 1;
			unsigned short ANSC005 : 1;
			unsigned short ANSC006 : 1;
			unsigned short ANSC007 : 1;
			unsigned short ANSC008 : 1;
			unsigned short ANSC009 : 1;
			unsigned short ANSC010 : 1;
			unsigned short ANSC011 : 1;
			unsigned short ANSC012 : 1;
			unsigned short ANSC013 : 1;
			unsigned short ANSC014 : 1;
			unsigned short ANSC015 : 1;
#else
			unsigned short ANSC015 : 1;
			unsigned short ANSC014 : 1;
			unsigned short ANSC013 : 1;
			unsigned short ANSC012 : 1;
			unsigned short ANSC011 : 1;
			unsigned short ANSC010 : 1;
			unsigned short ANSC009 : 1;
			unsigned short ANSC008 : 1;
			unsigned short ANSC007 : 1;
			unsigned short ANSC006 : 1;
			unsigned short ANSC005 : 1;
			unsigned short ANSC004 : 1;
			unsigned short ANSC003 : 1;
			unsigned short ANSC002 : 1;
			unsigned short ANSC001 : 1;
			unsigned short ANSC000 : 1;
#endif
	} BIT;
	} ADANSC0;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ANSC100 : 1;
			unsigned short ANSC101 : 1;
			unsigned short ANSC102 : 1;
			unsigned short ANSC103 : 1;
			unsigned short ANSC104 : 1;
			unsigned short  : 11;
#else
			unsigned short  : 11;
			unsigned short ANSC104 : 1;
			unsigned short ANSC103 : 1;
			unsigned short ANSC102 : 1;
			unsigned short ANSC101 : 1;
			unsigned short ANSC100 : 1;
#endif
	} BIT;
	} ADANSC1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TSSC : 1;
			unsigned char OCSC : 1;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char OCSC : 1;
			unsigned char TSSC : 1;
#endif
	} BIT;
	} ADGCEXCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TRSC : 6;
			unsigned char GCADIE : 1;
			unsigned char GRCE : 1;
#else
			unsigned char GRCE : 1;
			unsigned char GCADIE : 1;
			unsigned char TRSC : 6;
#endif
	} BIT;
	} ADGCTRGR;
	char           wk12[3];
	unsigned char  ADSSTRL;
	unsigned char  ADSSTRT;
	unsigned char  ADSSTRO;
	unsigned char  ADSSTR0;
	unsigned char  ADSSTR1;
	unsigned char  ADSSTR2;
	unsigned char  ADSSTR3;
	unsigned char  ADSSTR4;
	unsigned char  ADSSTR5;
	unsigned char  ADSSTR6;
	unsigned char  ADSSTR7;
	unsigned char  ADSSTR8;
	unsigned char  ADSSTR9;
	unsigned char  ADSSTR10;
	unsigned char  ADSSTR11;
	unsigned char  ADSSTR12;
	unsigned char  ADSSTR13;
	unsigned char  ADSSTR14;
	unsigned char  ADSSTR15;
} st_s12ad1_t;

typedef struct st_sci0 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CKS : 2;
			unsigned char MP : 1;
			unsigned char STOP : 1;
			unsigned char PM : 1;
			unsigned char PE : 1;
			unsigned char CHR : 1;
			unsigned char CM : 1;
#else
			unsigned char CM : 1;
			unsigned char CHR : 1;
			unsigned char PE : 1;
			unsigned char PM : 1;
			unsigned char STOP : 1;
			unsigned char MP : 1;
			unsigned char CKS : 2;
#endif
	} BIT;
	} SMR;
	unsigned char  BRR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CKE : 2;
			unsigned char TEIE : 1;
			unsigned char MPIE : 1;
			unsigned char RE : 1;
			unsigned char TE : 1;
			unsigned char RIE : 1;
			unsigned char TIE : 1;
#else
			unsigned char TIE : 1;
			unsigned char RIE : 1;
			unsigned char TE : 1;
			unsigned char RE : 1;
			unsigned char MPIE : 1;
			unsigned char TEIE : 1;
			unsigned char CKE : 2;
#endif
	} BIT;
	} SCR;
	unsigned char  TDR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MPBT : 1;
			unsigned char MPB : 1;
			unsigned char TEND : 1;
			unsigned char PER : 1;
			unsigned char FER : 1;
			unsigned char ORER : 1;
			unsigned char RDRF : 1;
			unsigned char TDRE : 1;
#else
			unsigned char TDRE : 1;
			unsigned char RDRF : 1;
			unsigned char ORER : 1;
			unsigned char FER : 1;
			unsigned char PER : 1;
			unsigned char TEND : 1;
			unsigned char MPB : 1;
			unsigned char MPBT : 1;
#endif
	} BIT;
	} SSR;
	unsigned char  RDR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SMIF : 1;
			unsigned char  : 1;
			unsigned char SINV : 1;
			unsigned char SDIR : 1;
			unsigned char CHR1 : 1;
			unsigned char  : 2;
			unsigned char BCP2 : 1;
#else
			unsigned char BCP2 : 1;
			unsigned char  : 2;
			unsigned char CHR1 : 1;
			unsigned char SDIR : 1;
			unsigned char SINV : 1;
			unsigned char  : 1;
			unsigned char SMIF : 1;
#endif
	} BIT;
	} SCMR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ACS0 : 1;
			unsigned char  : 1;
			unsigned char BRME : 1;
			unsigned char ABCSE : 1;
			unsigned char ABCS : 1;
			unsigned char NFEN : 1;
			unsigned char BGDM : 1;
			unsigned char RXDESEL : 1;
#else
			unsigned char RXDESEL : 1;
			unsigned char BGDM : 1;
			unsigned char NFEN : 1;
			unsigned char ABCS : 1;
			unsigned char ABCSE : 1;
			unsigned char BRME : 1;
			unsigned char  : 1;
			unsigned char ACS0 : 1;
#endif
	} BIT;
	} SEMR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFCS : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char NFCS : 3;
#endif
	} BIT;
	} SNFR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IICM : 1;
			unsigned char  : 2;
			unsigned char IICDL : 5;
#else
			unsigned char IICDL : 5;
			unsigned char  : 2;
			unsigned char IICM : 1;
#endif
	} BIT;
	} SIMR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IICINTM : 1;
			unsigned char IICCSC : 1;
			unsigned char  : 3;
			unsigned char IICACKT : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char IICACKT : 1;
			unsigned char  : 3;
			unsigned char IICCSC : 1;
			unsigned char IICINTM : 1;
#endif
	} BIT;
	} SIMR2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IICSTAREQ : 1;
			unsigned char IICRSTAREQ : 1;
			unsigned char IICSTPREQ : 1;
			unsigned char IICSTIF : 1;
			unsigned char IICSDAS : 2;
			unsigned char IICSCLS : 2;
#else
			unsigned char IICSCLS : 2;
			unsigned char IICSDAS : 2;
			unsigned char IICSTIF : 1;
			unsigned char IICSTPREQ : 1;
			unsigned char IICRSTAREQ : 1;
			unsigned char IICSTAREQ : 1;
#endif
	} BIT;
	} SIMR3;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IICACKR : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char IICACKR : 1;
#endif
	} BIT;
	} SISR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SSE : 1;
			unsigned char CTSE : 1;
			unsigned char MSS : 1;
			unsigned char  : 1;
			unsigned char MFF : 1;
			unsigned char  : 1;
			unsigned char CKPOL : 1;
			unsigned char CKPH : 1;
#else
			unsigned char CKPH : 1;
			unsigned char CKPOL : 1;
			unsigned char  : 1;
			unsigned char MFF : 1;
			unsigned char  : 1;
			unsigned char MSS : 1;
			unsigned char CTSE : 1;
			unsigned char SSE : 1;
#endif
	} BIT;
	} SPMR;
	union {
		unsigned short WORD;
		struct {
			unsigned char TDRH;
			unsigned char TDRL;
		} BYTE;
	} TDRHL;
	union {
		unsigned short WORD;
		struct {
			unsigned char RDRH;
			unsigned char RDRL;
		} BYTE;
	} RDRHL;
	unsigned char  MDDR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DCMF : 1;
			unsigned char  : 2;
			unsigned char DPER : 1;
			unsigned char DFER : 1;
			unsigned char  : 1;
			unsigned char IDSEL : 1;
			unsigned char DCME : 1;
#else
			unsigned char DCME : 1;
			unsigned char IDSEL : 1;
			unsigned char  : 1;
			unsigned char DFER : 1;
			unsigned char DPER : 1;
			unsigned char  : 2;
			unsigned char DCMF : 1;
#endif
	} BIT;
	} DCCR;
	char           wk0[6];
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CMPD : 9;
			unsigned short  : 7;
#else
			unsigned short  : 7;
			unsigned short CMPD : 9;
#endif
	} BIT;
	} CDR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char RXDMON : 1;
			unsigned char SPB2DT : 1;
			unsigned char SPB2IO : 1;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char SPB2IO : 1;
			unsigned char SPB2DT : 1;
			unsigned char RXDMON : 1;
#endif
	} BIT;
	} SPTR;
} st_sci0_t;

typedef struct st_sci7 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CKS : 2;
			unsigned char MP : 1;
			unsigned char STOP : 1;
			unsigned char PM : 1;
			unsigned char PE : 1;
			unsigned char CHR : 1;
			unsigned char CM : 1;
#else
			unsigned char CM : 1;
			unsigned char CHR : 1;
			unsigned char PE : 1;
			unsigned char PM : 1;
			unsigned char STOP : 1;
			unsigned char MP : 1;
			unsigned char CKS : 2;
#endif
	} BIT;
	} SMR;
	unsigned char  BRR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CKE : 2;
			unsigned char TEIE : 1;
			unsigned char MPIE : 1;
			unsigned char RE : 1;
			unsigned char TE : 1;
			unsigned char RIE : 1;
			unsigned char TIE : 1;
#else
			unsigned char TIE : 1;
			unsigned char RIE : 1;
			unsigned char TE : 1;
			unsigned char RE : 1;
			unsigned char MPIE : 1;
			unsigned char TEIE : 1;
			unsigned char CKE : 2;
#endif
	} BIT;
	} SCR;
	unsigned char  TDR;
	union {
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MPBT : 1;
			unsigned char MPB : 1;
			unsigned char TEND : 1;
			unsigned char PER : 1;
			unsigned char FER : 1;
			unsigned char ORER : 1;
			unsigned char RDRF : 1;
			unsigned char TDRE : 1;
#else
			unsigned char TDRE : 1;
			unsigned char RDRF : 1;
			unsigned char ORER : 1;
			unsigned char FER : 1;
			unsigned char PER : 1;
			unsigned char TEND : 1;
			unsigned char MPB : 1;
			unsigned char MPBT : 1;
#endif
	} BIT;
		} SSR;
		union {
			unsigned char BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DR : 1;
			unsigned char  : 1;
			unsigned char TEND : 1;
			unsigned char PER : 1;
			unsigned char FER : 1;
			unsigned char ORER : 1;
			unsigned char RDF : 1;
			unsigned char TDFE : 1;
#else
			unsigned char TDFE : 1;
			unsigned char RDF : 1;
			unsigned char ORER : 1;
			unsigned char FER : 1;
			unsigned char PER : 1;
			unsigned char TEND : 1;
			unsigned char  : 1;
			unsigned char DR : 1;
#endif
	} BIT;
		} SSRFIFO;
	};
	unsigned char  RDR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SMIF : 1;
			unsigned char  : 1;
			unsigned char SINV : 1;
			unsigned char SDIR : 1;
			unsigned char CHR1 : 1;
			unsigned char  : 2;
			unsigned char BCP2 : 1;
#else
			unsigned char BCP2 : 1;
			unsigned char  : 2;
			unsigned char CHR1 : 1;
			unsigned char SDIR : 1;
			unsigned char SINV : 1;
			unsigned char  : 1;
			unsigned char SMIF : 1;
#endif
	} BIT;
	} SCMR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ACS0 : 1;
			unsigned char  : 1;
			unsigned char BRME : 1;
			unsigned char ABCSE : 1;
			unsigned char ABCS : 1;
			unsigned char NFEN : 1;
			unsigned char BGDM : 1;
			unsigned char RXDESEL : 1;
#else
			unsigned char RXDESEL : 1;
			unsigned char BGDM : 1;
			unsigned char NFEN : 1;
			unsigned char ABCS : 1;
			unsigned char ABCSE : 1;
			unsigned char BRME : 1;
			unsigned char  : 1;
			unsigned char ACS0 : 1;
#endif
	} BIT;
	} SEMR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFCS : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char NFCS : 3;
#endif
	} BIT;
	} SNFR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IICM : 1;
			unsigned char  : 2;
			unsigned char IICDL : 5;
#else
			unsigned char IICDL : 5;
			unsigned char  : 2;
			unsigned char IICM : 1;
#endif
	} BIT;
	} SIMR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IICINTM : 1;
			unsigned char IICCSC : 1;
			unsigned char  : 3;
			unsigned char IICACKT : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char IICACKT : 1;
			unsigned char  : 3;
			unsigned char IICCSC : 1;
			unsigned char IICINTM : 1;
#endif
	} BIT;
	} SIMR2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IICSTAREQ : 1;
			unsigned char IICRSTAREQ : 1;
			unsigned char IICSTPREQ : 1;
			unsigned char IICSTIF : 1;
			unsigned char IICSDAS : 2;
			unsigned char IICSCLS : 2;
#else
			unsigned char IICSCLS : 2;
			unsigned char IICSDAS : 2;
			unsigned char IICSTIF : 1;
			unsigned char IICSTPREQ : 1;
			unsigned char IICRSTAREQ : 1;
			unsigned char IICSTAREQ : 1;
#endif
	} BIT;
	} SIMR3;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IICACKR : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char IICACKR : 1;
#endif
	} BIT;
	} SISR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SSE : 1;
			unsigned char CTSE : 1;
			unsigned char MSS : 1;
			unsigned char  : 1;
			unsigned char MFF : 1;
			unsigned char  : 1;
			unsigned char CKPOL : 1;
			unsigned char CKPH : 1;
#else
			unsigned char CKPH : 1;
			unsigned char CKPOL : 1;
			unsigned char  : 1;
			unsigned char MFF : 1;
			unsigned char  : 1;
			unsigned char MSS : 1;
			unsigned char CTSE : 1;
			unsigned char SSE : 1;
#endif
	} BIT;
	} SPMR;
	union {
		union {
			unsigned short WORD;
			struct {
				unsigned char TDRH;
				unsigned char TDRL;
			} BYTE;
		} TDRHL;
		union {
			unsigned short WORD;
			struct {
				unsigned char H;
				unsigned char L;
			} BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short TDAT : 9;
			unsigned short MPBT : 1;
			unsigned short  : 6;
#else
			unsigned short  : 6;
			unsigned short MPBT : 1;
			unsigned short TDAT : 9;
#endif
	} BIT;
		} FTDR;
	};
	union {
		union {
			unsigned short WORD;
			struct {
				unsigned char RDRH;
				unsigned char RDRL;
			} BYTE;
		} RDRHL;
		union {
			unsigned short WORD;
			struct {
				unsigned char H;
				unsigned char L;
			} BYTE;
			struct {
				
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short RDAT : 9;
			unsigned short MPB : 1;
			unsigned short DR : 1;
			unsigned short PER : 1;
			unsigned short FER : 1;
			unsigned short ORER : 1;
			unsigned short RDF : 1;
			unsigned short  : 1;
#else
			unsigned short  : 1;
			unsigned short RDF : 1;
			unsigned short ORER : 1;
			unsigned short FER : 1;
			unsigned short PER : 1;
			unsigned short DR : 1;
			unsigned short MPB : 1;
			unsigned short RDAT : 9;
#endif
	} BIT;
		} FRDR;
	};
	unsigned char  MDDR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DCMF : 1;
			unsigned char  : 2;
			unsigned char DPER : 1;
			unsigned char DFER : 1;
			unsigned char  : 1;
			unsigned char IDSEL : 1;
			unsigned char DCME : 1;
#else
			unsigned char DCME : 1;
			unsigned char IDSEL : 1;
			unsigned char  : 1;
			unsigned char DFER : 1;
			unsigned char DPER : 1;
			unsigned char  : 2;
			unsigned char DCMF : 1;
#endif
	} BIT;
	} DCCR;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short FM : 1;
			unsigned short RFRST : 1;
			unsigned short TFRST : 1;
			unsigned short DRES : 1;
			unsigned short TTRG : 4;
			unsigned short RTRG : 4;
			unsigned short RSTRG : 4;
#else
			unsigned short RSTRG : 4;
			unsigned short RTRG : 4;
			unsigned short TTRG : 4;
			unsigned short DRES : 1;
			unsigned short TFRST : 1;
			unsigned short RFRST : 1;
			unsigned short FM : 1;
#endif
	} BIT;
	} FCR;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short R : 5;
			unsigned short  : 3;
			unsigned short T : 5;
			unsigned short  : 3;
#else
			unsigned short  : 3;
			unsigned short T : 5;
			unsigned short  : 3;
			unsigned short R : 5;
#endif
	} BIT;
	} FDR;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ORER : 1;
			unsigned short  : 1;
			unsigned short FNUM : 5;
			unsigned short  : 1;
			unsigned short PNUM : 5;
			unsigned short  : 3;
#else
			unsigned short  : 3;
			unsigned short PNUM : 5;
			unsigned short  : 1;
			unsigned short FNUM : 5;
			unsigned short  : 1;
			unsigned short ORER : 1;
#endif
	} BIT;
	} LSR;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CMPD : 9;
			unsigned short  : 7;
#else
			unsigned short  : 7;
			unsigned short CMPD : 9;
#endif
	} BIT;
	} CDR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char RXDMON : 1;
			unsigned char SPB2DT : 1;
			unsigned char SPB2IO : 1;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char SPB2IO : 1;
			unsigned char SPB2DT : 1;
			unsigned char RXDMON : 1;
#endif
	} BIT;
	} SPTR;
} st_sci7_t;

typedef struct st_sci12 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CKS : 2;
			unsigned char MP : 1;
			unsigned char STOP : 1;
			unsigned char PM : 1;
			unsigned char PE : 1;
			unsigned char CHR : 1;
			unsigned char CM : 1;
#else
			unsigned char CM : 1;
			unsigned char CHR : 1;
			unsigned char PE : 1;
			unsigned char PM : 1;
			unsigned char STOP : 1;
			unsigned char MP : 1;
			unsigned char CKS : 2;
#endif
	} BIT;
	} SMR;
	unsigned char  BRR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CKE : 2;
			unsigned char TEIE : 1;
			unsigned char MPIE : 1;
			unsigned char RE : 1;
			unsigned char TE : 1;
			unsigned char RIE : 1;
			unsigned char TIE : 1;
#else
			unsigned char TIE : 1;
			unsigned char RIE : 1;
			unsigned char TE : 1;
			unsigned char RE : 1;
			unsigned char MPIE : 1;
			unsigned char TEIE : 1;
			unsigned char CKE : 2;
#endif
	} BIT;
	} SCR;
	unsigned char  TDR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MPBT : 1;
			unsigned char MPB : 1;
			unsigned char TEND : 1;
			unsigned char PER : 1;
			unsigned char FER : 1;
			unsigned char ORER : 1;
			unsigned char RDRF : 1;
			unsigned char TDRE : 1;
#else
			unsigned char TDRE : 1;
			unsigned char RDRF : 1;
			unsigned char ORER : 1;
			unsigned char FER : 1;
			unsigned char PER : 1;
			unsigned char TEND : 1;
			unsigned char MPB : 1;
			unsigned char MPBT : 1;
#endif
	} BIT;
	} SSR;
	unsigned char  RDR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SMIF : 1;
			unsigned char  : 1;
			unsigned char SINV : 1;
			unsigned char SDIR : 1;
			unsigned char CHR1 : 1;
			unsigned char  : 2;
			unsigned char BCP2 : 1;
#else
			unsigned char BCP2 : 1;
			unsigned char  : 2;
			unsigned char CHR1 : 1;
			unsigned char SDIR : 1;
			unsigned char SINV : 1;
			unsigned char  : 1;
			unsigned char SMIF : 1;
#endif
	} BIT;
	} SCMR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ACS0 : 1;
			unsigned char  : 1;
			unsigned char BRME : 1;
			unsigned char  : 1;
			unsigned char ABCS : 1;
			unsigned char NFEN : 1;
			unsigned char BGDM : 1;
			unsigned char RXDESEL : 1;
#else
			unsigned char RXDESEL : 1;
			unsigned char BGDM : 1;
			unsigned char NFEN : 1;
			unsigned char ABCS : 1;
			unsigned char  : 1;
			unsigned char BRME : 1;
			unsigned char  : 1;
			unsigned char ACS0 : 1;
#endif
	} BIT;
	} SEMR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFCS : 3;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char NFCS : 3;
#endif
	} BIT;
	} SNFR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IICM : 1;
			unsigned char  : 2;
			unsigned char IICDL : 5;
#else
			unsigned char IICDL : 5;
			unsigned char  : 2;
			unsigned char IICM : 1;
#endif
	} BIT;
	} SIMR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IICINTM : 1;
			unsigned char IICCSC : 1;
			unsigned char  : 3;
			unsigned char IICACKT : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char IICACKT : 1;
			unsigned char  : 3;
			unsigned char IICCSC : 1;
			unsigned char IICINTM : 1;
#endif
	} BIT;
	} SIMR2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IICSTAREQ : 1;
			unsigned char IICRSTAREQ : 1;
			unsigned char IICSTPREQ : 1;
			unsigned char IICSTIF : 1;
			unsigned char IICSDAS : 2;
			unsigned char IICSCLS : 2;
#else
			unsigned char IICSCLS : 2;
			unsigned char IICSDAS : 2;
			unsigned char IICSTIF : 1;
			unsigned char IICSTPREQ : 1;
			unsigned char IICRSTAREQ : 1;
			unsigned char IICSTAREQ : 1;
#endif
	} BIT;
	} SIMR3;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IICACKR : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char IICACKR : 1;
#endif
	} BIT;
	} SISR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SSE : 1;
			unsigned char CTSE : 1;
			unsigned char MSS : 1;
			unsigned char  : 1;
			unsigned char MFF : 1;
			unsigned char  : 1;
			unsigned char CKPOL : 1;
			unsigned char CKPH : 1;
#else
			unsigned char CKPH : 1;
			unsigned char CKPOL : 1;
			unsigned char  : 1;
			unsigned char MFF : 1;
			unsigned char  : 1;
			unsigned char MSS : 1;
			unsigned char CTSE : 1;
			unsigned char SSE : 1;
#endif
	} BIT;
	} SPMR;
	union {
		unsigned short WORD;
		struct {
			unsigned char TDRH;
			unsigned char TDRL;
		} BYTE;
	} TDRHL;
	union {
		unsigned short WORD;
		struct {
			unsigned char RDRH;
			unsigned char RDRL;
		} BYTE;
	} RDRHL;
	unsigned char  MDDR;
	char           wk0[13];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ESME : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char ESME : 1;
#endif
	} BIT;
	} ESMER;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 1;
			unsigned char SFSF : 1;
			unsigned char RXDSF : 1;
			unsigned char BRME : 1;
			unsigned char  : 4;
#else
			unsigned char  : 4;
			unsigned char BRME : 1;
			unsigned char RXDSF : 1;
			unsigned char SFSF : 1;
			unsigned char  : 1;
#endif
	} BIT;
	} CR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BFE : 1;
			unsigned char CF0RE : 1;
			unsigned char CF1DS : 2;
			unsigned char PIBE : 1;
			unsigned char PIBS : 3;
#else
			unsigned char PIBS : 3;
			unsigned char PIBE : 1;
			unsigned char CF1DS : 2;
			unsigned char CF0RE : 1;
			unsigned char BFE : 1;
#endif
	} BIT;
	} CR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DFCS : 3;
			unsigned char  : 1;
			unsigned char BCCS : 2;
			unsigned char RTS : 2;
#else
			unsigned char RTS : 2;
			unsigned char BCCS : 2;
			unsigned char  : 1;
			unsigned char DFCS : 3;
#endif
	} BIT;
	} CR2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SDST : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char SDST : 1;
#endif
	} BIT;
	} CR3;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TXDXPS : 1;
			unsigned char RXDXPS : 1;
			unsigned char  : 2;
			unsigned char SHARPS : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char SHARPS : 1;
			unsigned char  : 2;
			unsigned char RXDXPS : 1;
			unsigned char TXDXPS : 1;
#endif
	} BIT;
	} PCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BFDIE : 1;
			unsigned char CF0MIE : 1;
			unsigned char CF1MIE : 1;
			unsigned char PIBDIE : 1;
			unsigned char BCDIE : 1;
			unsigned char AEDIE : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char AEDIE : 1;
			unsigned char BCDIE : 1;
			unsigned char PIBDIE : 1;
			unsigned char CF1MIE : 1;
			unsigned char CF0MIE : 1;
			unsigned char BFDIE : 1;
#endif
	} BIT;
	} ICR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BFDF : 1;
			unsigned char CF0MF : 1;
			unsigned char CF1MF : 1;
			unsigned char PIBDF : 1;
			unsigned char BCDF : 1;
			unsigned char AEDF : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char AEDF : 1;
			unsigned char BCDF : 1;
			unsigned char PIBDF : 1;
			unsigned char CF1MF : 1;
			unsigned char CF0MF : 1;
			unsigned char BFDF : 1;
#endif
	} BIT;
	} STR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BFDCL : 1;
			unsigned char CF0MCL : 1;
			unsigned char CF1MCL : 1;
			unsigned char PIBDCL : 1;
			unsigned char BCDCL : 1;
			unsigned char AEDCL : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char AEDCL : 1;
			unsigned char BCDCL : 1;
			unsigned char PIBDCL : 1;
			unsigned char CF1MCL : 1;
			unsigned char CF0MCL : 1;
			unsigned char BFDCL : 1;
#endif
	} BIT;
	} STCR;
	unsigned char  CF0DR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CF0CE0 : 1;
			unsigned char CF0CE1 : 1;
			unsigned char CF0CE2 : 1;
			unsigned char CF0CE3 : 1;
			unsigned char CF0CE4 : 1;
			unsigned char CF0CE5 : 1;
			unsigned char CF0CE6 : 1;
			unsigned char CF0CE7 : 1;
#else
			unsigned char CF0CE7 : 1;
			unsigned char CF0CE6 : 1;
			unsigned char CF0CE5 : 1;
			unsigned char CF0CE4 : 1;
			unsigned char CF0CE3 : 1;
			unsigned char CF0CE2 : 1;
			unsigned char CF0CE1 : 1;
			unsigned char CF0CE0 : 1;
#endif
	} BIT;
	} CF0CR;
	unsigned char  CF0RR;
	unsigned char  PCF1DR;
	unsigned char  SCF1DR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CF1CE0 : 1;
			unsigned char CF1CE1 : 1;
			unsigned char CF1CE2 : 1;
			unsigned char CF1CE3 : 1;
			unsigned char CF1CE4 : 1;
			unsigned char CF1CE5 : 1;
			unsigned char CF1CE6 : 1;
			unsigned char CF1CE7 : 1;
#else
			unsigned char CF1CE7 : 1;
			unsigned char CF1CE6 : 1;
			unsigned char CF1CE5 : 1;
			unsigned char CF1CE4 : 1;
			unsigned char CF1CE3 : 1;
			unsigned char CF1CE2 : 1;
			unsigned char CF1CE1 : 1;
			unsigned char CF1CE0 : 1;
#endif
	} BIT;
	} CF1CR;
	unsigned char  CF1RR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TCST : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char TCST : 1;
#endif
	} BIT;
	} TCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TOMS : 2;
			unsigned char  : 1;
			unsigned char TWRC : 1;
			unsigned char TCSS : 3;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char TCSS : 3;
			unsigned char TWRC : 1;
			unsigned char  : 1;
			unsigned char TOMS : 2;
#endif
	} BIT;
	} TMR;
	unsigned char  TPRE;
	unsigned char  TCNT;
} st_sci12_t;

typedef struct st_sdhi {
	union {
		unsigned long LONG;
#ifdef IODEFINE_H_HISTORY
		struct {
			unsigned long :16;
			unsigned long CMD12AT:2;
			unsigned long TRSTP:1;
			unsigned long CMDRW:1;
			unsigned long CMDTP:1;
			unsigned long RSPTP:3;
			unsigned long ACMD:2;
			unsigned long CMDIDX:6;
		} BIT;
#endif
	} SDCMD;
	char           wk0[4];
	unsigned long  SDARG;
	char           wk1[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long STP : 1;
			unsigned long  : 7;
			unsigned long SDBLKCNTEN : 1;
			unsigned long  : 23;
#else
			unsigned long  : 23;
			unsigned long SDBLKCNTEN : 1;
			unsigned long  : 7;
			unsigned long STP : 1;
#endif
	} BIT;
	} SDSTOP;
	unsigned long  SDBLKCNT;
	unsigned long  SDRSP10;
	char           wk2[4];
	unsigned long  SDRSP32;
	char           wk3[4];
	unsigned long  SDRSP54;
	char           wk4[4];
	unsigned long  SDRSP76;
	char           wk5[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RSPEND : 1;
			unsigned long  : 1;
			unsigned long ACEND : 1;
			unsigned long SDCDRM : 1;
			unsigned long SDCDIN : 1;
			unsigned long SDCDMON : 1;
			unsigned long  : 1;
			unsigned long SDWPMON : 1;
			unsigned long SDD3RM : 1;
			unsigned long SDD3IN : 1;
			unsigned long SDD3MON : 1;
			unsigned long  : 21;
#else
			unsigned long  : 21;
			unsigned long SDD3MON : 1;
			unsigned long SDD3IN : 1;
			unsigned long SDD3RM : 1;
			unsigned long SDWPMON : 1;
			unsigned long  : 1;
			unsigned long SDCDMON : 1;
			unsigned long SDCDIN : 1;
			unsigned long SDCDRM : 1;
			unsigned long ACEND : 1;
			unsigned long  : 1;
			unsigned long RSPEND : 1;
#endif
	} BIT;
	} SDSTS1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CMDE : 1;
			unsigned long CRCE : 1;
			unsigned long ENDE : 1;
			unsigned long DTO : 1;
			unsigned long ILW : 1;
			unsigned long ILR : 1;
			unsigned long RSPTO : 1;
			unsigned long SDD0MON : 1;
			unsigned long BRE : 1;
			unsigned long BWE : 1;
			unsigned long  : 3;
			unsigned long SDCLKCREN : 1;
			unsigned long CBSY : 1;
			unsigned long ILA : 1;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long ILA : 1;
			unsigned long CBSY : 1;
			unsigned long SDCLKCREN : 1;
			unsigned long  : 3;
			unsigned long BWE : 1;
			unsigned long BRE : 1;
			unsigned long SDD0MON : 1;
			unsigned long RSPTO : 1;
			unsigned long ILR : 1;
			unsigned long ILW : 1;
			unsigned long DTO : 1;
			unsigned long ENDE : 1;
			unsigned long CRCE : 1;
			unsigned long CMDE : 1;
#endif
	} BIT;
	} SDSTS2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RSPENDM : 1;
			unsigned long  : 1;
			unsigned long ACENDM : 1;
			unsigned long SDCDRMM : 1;
			unsigned long SDCDINM : 1;
			unsigned long  : 3;
			unsigned long SDD3RMM : 1;
			unsigned long SDD3INM : 1;
			unsigned long  : 22;
#else
			unsigned long  : 22;
			unsigned long SDD3INM : 1;
			unsigned long SDD3RMM : 1;
			unsigned long  : 3;
			unsigned long SDCDINM : 1;
			unsigned long SDCDRMM : 1;
			unsigned long ACENDM : 1;
			unsigned long  : 1;
			unsigned long RSPENDM : 1;
#endif
	} BIT;
	} SDIMSK1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CMDEM : 1;
			unsigned long CRCEM : 1;
			unsigned long ENDEM : 1;
			unsigned long DTTOM : 1;
			unsigned long ILWM : 1;
			unsigned long ILRM : 1;
			unsigned long RSPTOM : 1;
			unsigned long  : 1;
			unsigned long BREM : 1;
			unsigned long BWEM : 1;
			unsigned long  : 5;
			unsigned long ILAM : 1;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long ILAM : 1;
			unsigned long  : 5;
			unsigned long BWEM : 1;
			unsigned long BREM : 1;
			unsigned long  : 1;
			unsigned long RSPTOM : 1;
			unsigned long ILRM : 1;
			unsigned long ILWM : 1;
			unsigned long DTTOM : 1;
			unsigned long ENDEM : 1;
			unsigned long CRCEM : 1;
			unsigned long CMDEM : 1;
#endif
	} BIT;
	} SDIMSK2;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CLKSEL : 8;
			unsigned long CLKEN : 1;
			unsigned long CLKCTRLEN : 1;
			unsigned long  : 22;
#else
			unsigned long  : 22;
			unsigned long CLKCTRLEN : 1;
			unsigned long CLKEN : 1;
			unsigned long CLKSEL : 8;
#endif
	} BIT;
	} SDCLKCR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long LEN : 10;
			unsigned long  : 22;
#else
			unsigned long  : 22;
			unsigned long LEN : 10;
#endif
	} BIT;
	} SDSIZE;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CTOP : 4;
			unsigned long TOP : 4;
			unsigned long  : 7;
			unsigned long WIDTH : 1;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long WIDTH : 1;
			unsigned long  : 7;
			unsigned long TOP : 4;
			unsigned long CTOP : 4;
#endif
	} BIT;
	} SDOPT;
	char           wk6[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long CMDE0 : 1;
			unsigned long CMDE1 : 1;
			unsigned long RSPLENE0 : 1;
			unsigned long RSPLENE1 : 1;
			unsigned long RDLENE : 1;
			unsigned long CRCLENE : 1;
			unsigned long  : 2;
			unsigned long RSPCRCE0 : 1;
			unsigned long RSPCRCE1 : 1;
			unsigned long RDCRCE : 1;
			unsigned long CRCTKE : 1;
			unsigned long CRCTK : 3;
			unsigned long  : 17;
#else
			unsigned long  : 17;
			unsigned long CRCTK : 3;
			unsigned long CRCTKE : 1;
			unsigned long RDCRCE : 1;
			unsigned long RSPCRCE1 : 1;
			unsigned long RSPCRCE0 : 1;
			unsigned long  : 2;
			unsigned long CRCLENE : 1;
			unsigned long RDLENE : 1;
			unsigned long RSPLENE1 : 1;
			unsigned long RSPLENE0 : 1;
			unsigned long CMDE1 : 1;
			unsigned long CMDE0 : 1;
#endif
	} BIT;
	} SDERSTS1;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RSPTO0 : 1;
			unsigned long RSPTO1 : 1;
			unsigned long BSYTO0 : 1;
			unsigned long BSYTO1 : 1;
			unsigned long RDTO : 1;
			unsigned long CRCTO : 1;
			unsigned long CRCBSYTO : 1;
			unsigned long  : 25;
#else
			unsigned long  : 25;
			unsigned long CRCBSYTO : 1;
			unsigned long CRCTO : 1;
			unsigned long RDTO : 1;
			unsigned long BSYTO1 : 1;
			unsigned long BSYTO0 : 1;
			unsigned long RSPTO1 : 1;
			unsigned long RSPTO0 : 1;
#endif
	} BIT;
	} SDERSTS2;
	unsigned long  SDBUFR;
	char           wk7[4];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long INTEN : 1;
			unsigned long  : 1;
			unsigned long RWREQ : 1;
			unsigned long  : 5;
			unsigned long IOABT : 1;
			unsigned long C52PUB : 1;
			unsigned long  : 22;
#else
			unsigned long  : 22;
			unsigned long C52PUB : 1;
			unsigned long IOABT : 1;
			unsigned long  : 5;
			unsigned long RWREQ : 1;
			unsigned long  : 1;
			unsigned long INTEN : 1;
#endif
	} BIT;
	} SDIOMD;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long IOIRQ : 1;
			unsigned long  : 13;
			unsigned long EXPUB52 : 1;
			unsigned long EXWT : 1;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long EXWT : 1;
			unsigned long EXPUB52 : 1;
			unsigned long  : 13;
			unsigned long IOIRQ : 1;
#endif
	} BIT;
	} SDIOSTS;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long IOIRQM : 1;
			unsigned long  : 13;
			unsigned long EXPUB52M : 1;
			unsigned long EXWTM : 1;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long EXWTM : 1;
			unsigned long EXPUB52M : 1;
			unsigned long  : 13;
			unsigned long IOIRQM : 1;
#endif
	} BIT;
	} SDIOIMSK;
	char           wk8[316];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 1;
			unsigned long DMAEN : 1;
			unsigned long  : 30;
#else
			unsigned long  : 30;
			unsigned long DMAEN : 1;
			unsigned long  : 1;
#endif
	} BIT;
	} SDDMAEN;
	char           wk9[12];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long SDRST : 1;
			unsigned long  : 31;
#else
			unsigned long  : 31;
			unsigned long SDRST : 1;
#endif
	} BIT;
	} SDRST;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long IP1 : 8;
			unsigned long IP2 : 4;
			unsigned long  : 2;
			unsigned long CLKRAT : 1;
			unsigned long CPRM : 1;
			unsigned long  : 16;
#else
			unsigned long  : 16;
			unsigned long CPRM : 1;
			unsigned long CLKRAT : 1;
			unsigned long  : 2;
			unsigned long IP2 : 4;
			unsigned long IP1 : 8;
#endif
	} BIT;
	} SDVER;
	char           wk10[24];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 6;
			unsigned long BWSWP : 1;
			unsigned long BRSWP : 1;
			unsigned long  : 24;
#else
			unsigned long  : 24;
			unsigned long BRSWP : 1;
			unsigned long BWSWP : 1;
			unsigned long  : 6;
#endif
	} BIT;
	} SDSWAP;
} st_sdhi_t;

typedef struct st_smci {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CKS : 2;
			unsigned char BCP : 2;
			unsigned char PM : 1;
			unsigned char PE : 1;
			unsigned char BLK : 1;
			unsigned char GM : 1;
#else
			unsigned char GM : 1;
			unsigned char BLK : 1;
			unsigned char PE : 1;
			unsigned char PM : 1;
			unsigned char BCP : 2;
			unsigned char CKS : 2;
#endif
	} BIT;
	} SMR;
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CKE : 2;
			unsigned char TEIE : 1;
			unsigned char MPIE : 1;
			unsigned char RE : 1;
			unsigned char TE : 1;
			unsigned char RIE : 1;
			unsigned char TIE : 1;
#else
			unsigned char TIE : 1;
			unsigned char RIE : 1;
			unsigned char TE : 1;
			unsigned char RE : 1;
			unsigned char MPIE : 1;
			unsigned char TEIE : 1;
			unsigned char CKE : 2;
#endif
	} BIT;
	} SCR;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MPBT : 1;
			unsigned char MPB : 1;
			unsigned char TEND : 1;
			unsigned char PER : 1;
			unsigned char ERS : 1;
			unsigned char ORER : 1;
			unsigned char RDRF : 1;
			unsigned char TDRE : 1;
#else
			unsigned char TDRE : 1;
			unsigned char RDRF : 1;
			unsigned char ORER : 1;
			unsigned char ERS : 1;
			unsigned char PER : 1;
			unsigned char TEND : 1;
			unsigned char MPB : 1;
			unsigned char MPBT : 1;
#endif
	} BIT;
	} SSR;
	char           wk2[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SMIF : 1;
			unsigned char  : 1;
			unsigned char SINV : 1;
			unsigned char SDIR : 1;
			unsigned char CHR1 : 1;
			unsigned char  : 2;
			unsigned char BCP2 : 1;
#else
			unsigned char BCP2 : 1;
			unsigned char  : 2;
			unsigned char CHR1 : 1;
			unsigned char SDIR : 1;
			unsigned char SINV : 1;
			unsigned char  : 1;
			unsigned char SMIF : 1;
#endif
	} BIT;
	} SCMR;
} st_smci_t;

typedef struct st_ssie {
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long REN : 1;
			unsigned long TEN : 1;
			unsigned long  : 1;
			unsigned long MUEN : 1;
			unsigned long CKDV : 4;
			unsigned long DEL : 1;
			unsigned long PDTA : 1;
			unsigned long SDTA : 1;
			unsigned long SPDP : 1;
			unsigned long LRCKP : 1;
			unsigned long BCKP : 1;
			unsigned long MST : 1;
			unsigned long  : 1;
			unsigned long SWL : 3;
			unsigned long DWL : 3;
			unsigned long FRM : 2;
			unsigned long  : 1;
			unsigned long IIEN : 1;
			unsigned long ROIEN : 1;
			unsigned long RUIEN : 1;
			unsigned long TOIEN : 1;
			unsigned long TUIEN : 1;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long TUIEN : 1;
			unsigned long TOIEN : 1;
			unsigned long RUIEN : 1;
			unsigned long ROIEN : 1;
			unsigned long IIEN : 1;
			unsigned long  : 1;
			unsigned long FRM : 2;
			unsigned long DWL : 3;
			unsigned long SWL : 3;
			unsigned long  : 1;
			unsigned long MST : 1;
			unsigned long BCKP : 1;
			unsigned long LRCKP : 1;
			unsigned long SPDP : 1;
			unsigned long SDTA : 1;
			unsigned long PDTA : 1;
			unsigned long DEL : 1;
			unsigned long CKDV : 4;
			unsigned long MUEN : 1;
			unsigned long  : 1;
			unsigned long TEN : 1;
			unsigned long REN : 1;
#endif
	} BIT;
	} SSICR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long  : 25;
			unsigned long IIRQ : 1;
			unsigned long ROIRQ : 1;
			unsigned long RUIRQ : 1;
			unsigned long TOIRQ : 1;
			unsigned long TUIRQ : 1;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long TUIRQ : 1;
			unsigned long TOIRQ : 1;
			unsigned long RUIRQ : 1;
			unsigned long ROIRQ : 1;
			unsigned long IIRQ : 1;
			unsigned long  : 25;
#endif
	} BIT;
	} SSISR;
	char           wk0[8];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RFRST : 1;
			unsigned long TFRST : 1;
			unsigned long RIE : 1;
			unsigned long TIE : 1;
			unsigned long  : 7;
			unsigned long BSW : 1;
			unsigned long  : 4;
			unsigned long SSIRST : 1;
			unsigned long  : 14;
			unsigned long AUCKE : 1;
#else
			unsigned long AUCKE : 1;
			unsigned long  : 14;
			unsigned long SSIRST : 1;
			unsigned long  : 4;
			unsigned long BSW : 1;
			unsigned long  : 7;
			unsigned long TIE : 1;
			unsigned long RIE : 1;
			unsigned long TFRST : 1;
			unsigned long RFRST : 1;
#endif
	} BIT;
	} SSIFCR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RDF : 1;
			unsigned long  : 7;
			unsigned long RDC : 6;
			unsigned long  : 2;
			unsigned long TDE : 1;
			unsigned long  : 7;
			unsigned long TDC : 6;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long TDC : 6;
			unsigned long  : 7;
			unsigned long TDE : 1;
			unsigned long  : 2;
			unsigned long RDC : 6;
			unsigned long  : 7;
			unsigned long RDF : 1;
#endif
	} BIT;
	} SSIFSR;
	union {
		unsigned long LONG;
		struct {
			unsigned short H;
		} WORD;
		struct {
			unsigned char HH;
		} BYTE;
	} SSIFTDR;
	union {
		unsigned long LONG;
		struct {
			unsigned short H;
		} WORD;
		struct {
			unsigned char HH;
		} BYTE;
	} SSIFRDR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long OMOD : 2;
			unsigned long  : 6;
			unsigned long LRCONT : 1;
			unsigned long BCKASTP : 1;
			unsigned long  : 22;
#else
			unsigned long  : 22;
			unsigned long BCKASTP : 1;
			unsigned long LRCONT : 1;
			unsigned long  : 6;
			unsigned long OMOD : 2;
#endif
	} BIT;
	} SSIOFR;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long RDFS : 5;
			unsigned long  : 3;
			unsigned long TDES : 5;
			unsigned long  : 19;
#else
			unsigned long  : 19;
			unsigned long TDES : 5;
			unsigned long  : 3;
			unsigned long RDFS : 5;
#endif
	} BIT;
	} SSISCR;
} st_ssie_t;

typedef struct st_system {
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short MD : 1;
			unsigned short  : 15;
#else
			unsigned short  : 15;
			unsigned short MD : 1;
#endif
	} BIT;
	} MDMONR;
	char           wk0[4];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short ROME : 1;
			unsigned short EXBE : 1;
			unsigned short  : 6;
			unsigned short KEY : 8;
#else
			unsigned short KEY : 8;
			unsigned short  : 6;
			unsigned short EXBE : 1;
			unsigned short ROME : 1;
#endif
	} BIT;
	} SYSCR0;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short RAME : 1;
			unsigned short  : 5;
			unsigned short ECCRAME : 1;
			unsigned short SBYRAME : 1;
			unsigned short  : 8;
#else
			unsigned short  : 8;
			unsigned short SBYRAME : 1;
			unsigned short ECCRAME : 1;
			unsigned short  : 5;
			unsigned short RAME : 1;
#endif
	} BIT;
	} SYSCR1;
	char           wk1[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 14;
			unsigned short OPE : 1;
			unsigned short SSBY : 1;
#else
			unsigned short SSBY : 1;
			unsigned short OPE : 1;
			unsigned short  : 14;
#endif
	} BIT;
	} SBYCR;
	char           wk2[2];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MSTPA0 : 1;
			unsigned long MSTPA1 : 1;
			unsigned long  : 2;
			unsigned long MSTPA4 : 1;
			unsigned long MSTPA5 : 1;
			unsigned long  : 1;
			unsigned long MSTPA7 : 1;
			unsigned long  : 1;
			unsigned long MSTPA9 : 1;
			unsigned long MSTPA10 : 1;
			unsigned long MSTPA11 : 1;
			unsigned long  : 1;
			unsigned long MSTPA13 : 1;
			unsigned long MSTPA14 : 1;
			unsigned long MSTPA15 : 1;
			unsigned long MSTPA16 : 1;
			unsigned long MSTPA17 : 1;
			unsigned long  : 1;
			unsigned long MSTPA19 : 1;
			unsigned long  : 4;
			unsigned long MSTPA24 : 1;
			unsigned long  : 2;
			unsigned long MSTPA27 : 1;
			unsigned long MSTPA28 : 1;
			unsigned long MSTPA29 : 1;
			unsigned long  : 1;
			unsigned long ACSE : 1;
#else
			unsigned long ACSE : 1;
			unsigned long  : 1;
			unsigned long MSTPA29 : 1;
			unsigned long MSTPA28 : 1;
			unsigned long MSTPA27 : 1;
			unsigned long  : 2;
			unsigned long MSTPA24 : 1;
			unsigned long  : 4;
			unsigned long MSTPA19 : 1;
			unsigned long  : 1;
			unsigned long MSTPA17 : 1;
			unsigned long MSTPA16 : 1;
			unsigned long MSTPA15 : 1;
			unsigned long MSTPA14 : 1;
			unsigned long MSTPA13 : 1;
			unsigned long  : 1;
			unsigned long MSTPA11 : 1;
			unsigned long MSTPA10 : 1;
			unsigned long MSTPA9 : 1;
			unsigned long  : 1;
			unsigned long MSTPA7 : 1;
			unsigned long  : 1;
			unsigned long MSTPA5 : 1;
			unsigned long MSTPA4 : 1;
			unsigned long  : 2;
			unsigned long MSTPA1 : 1;
			unsigned long MSTPA0 : 1;
#endif
	} BIT;
	} MSTPCRA;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MSTPB0 : 1;
			unsigned long MSTPB1 : 1;
			unsigned long MSTPB2 : 1;
			unsigned long  : 1;
			unsigned long MSTPB4 : 1;
			unsigned long  : 1;
			unsigned long MSTPB6 : 1;
			unsigned long  : 1;
			unsigned long MSTPB8 : 1;
			unsigned long MSTPB9 : 1;
			unsigned long  : 3;
			unsigned long MSTPB13 : 1;
			unsigned long MSTPB14 : 1;
			unsigned long MSTPB15 : 1;
			unsigned long MSTPB16 : 1;
			unsigned long MSTPB17 : 1;
			unsigned long  : 1;
			unsigned long MSTPB19 : 1;
			unsigned long MSTPB20 : 1;
			unsigned long MSTPB21 : 1;
			unsigned long MSTPB22 : 1;
			unsigned long MSTPB23 : 1;
			unsigned long MSTPB24 : 1;
			unsigned long MSTPB25 : 1;
			unsigned long MSTPB26 : 1;
			unsigned long MSTPB27 : 1;
			unsigned long MSTPB28 : 1;
			unsigned long MSTPB29 : 1;
			unsigned long MSTPB30 : 1;
			unsigned long MSTPB31 : 1;
#else
			unsigned long MSTPB31 : 1;
			unsigned long MSTPB30 : 1;
			unsigned long MSTPB29 : 1;
			unsigned long MSTPB28 : 1;
			unsigned long MSTPB27 : 1;
			unsigned long MSTPB26 : 1;
			unsigned long MSTPB25 : 1;
			unsigned long MSTPB24 : 1;
			unsigned long MSTPB23 : 1;
			unsigned long MSTPB22 : 1;
			unsigned long MSTPB21 : 1;
			unsigned long MSTPB20 : 1;
			unsigned long MSTPB19 : 1;
			unsigned long  : 1;
			unsigned long MSTPB17 : 1;
			unsigned long MSTPB16 : 1;
			unsigned long MSTPB15 : 1;
			unsigned long MSTPB14 : 1;
			unsigned long MSTPB13 : 1;
			unsigned long  : 3;
			unsigned long MSTPB9 : 1;
			unsigned long MSTPB8 : 1;
			unsigned long  : 1;
			unsigned long MSTPB6 : 1;
			unsigned long  : 1;
			unsigned long MSTPB4 : 1;
			unsigned long  : 1;
			unsigned long MSTPB2 : 1;
			unsigned long MSTPB1 : 1;
			unsigned long MSTPB0 : 1;
#endif
	} BIT;
	} MSTPCRB;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MSTPC0 : 1;
			unsigned long  : 1;
			unsigned long MSTPC2 : 1;
			unsigned long  : 3;
			unsigned long MSTPC6 : 1;
			unsigned long MSTPC7 : 1;
			unsigned long  : 9;
			unsigned long MSTPC17 : 1;
			unsigned long  : 1;
			unsigned long MSTPC19 : 1;
			unsigned long  : 2;
			unsigned long MSTPC22 : 1;
			unsigned long MSTPC23 : 1;
			unsigned long MSTPC24 : 1;
			unsigned long MSTPC25 : 1;
			unsigned long MSTPC26 : 1;
			unsigned long MSTPC27 : 1;
			unsigned long MSTPC28 : 1;
			unsigned long MSTPC29 : 1;
			unsigned long  : 2;
#else
			unsigned long  : 2;
			unsigned long MSTPC29 : 1;
			unsigned long MSTPC28 : 1;
			unsigned long MSTPC27 : 1;
			unsigned long MSTPC26 : 1;
			unsigned long MSTPC25 : 1;
			unsigned long MSTPC24 : 1;
			unsigned long MSTPC23 : 1;
			unsigned long MSTPC22 : 1;
			unsigned long  : 2;
			unsigned long MSTPC19 : 1;
			unsigned long  : 1;
			unsigned long MSTPC17 : 1;
			unsigned long  : 9;
			unsigned long MSTPC7 : 1;
			unsigned long MSTPC6 : 1;
			unsigned long  : 3;
			unsigned long MSTPC2 : 1;
			unsigned long  : 1;
			unsigned long MSTPC0 : 1;
#endif
	} BIT;
	} MSTPCRC;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long MSTPD0 : 1;
			unsigned long MSTPD1 : 1;
			unsigned long MSTPD2 : 1;
			unsigned long MSTPD3 : 1;
			unsigned long MSTPD4 : 1;
			unsigned long MSTPD5 : 1;
			unsigned long MSTPD6 : 1;
			unsigned long MSTPD7 : 1;
			unsigned long  : 6;
			unsigned long MSTPD14 : 1;
			unsigned long MSTPD15 : 1;
			unsigned long  : 3;
			unsigned long MSTPD19 : 1;
			unsigned long  : 1;
			unsigned long MSTPD21 : 1;
			unsigned long  : 5;
			unsigned long MSTPD27 : 1;
			unsigned long  : 4;
#else
			unsigned long  : 4;
			unsigned long MSTPD27 : 1;
			unsigned long  : 5;
			unsigned long MSTPD21 : 1;
			unsigned long  : 1;
			unsigned long MSTPD19 : 1;
			unsigned long  : 3;
			unsigned long MSTPD15 : 1;
			unsigned long MSTPD14 : 1;
			unsigned long  : 6;
			unsigned long MSTPD7 : 1;
			unsigned long MSTPD6 : 1;
			unsigned long MSTPD5 : 1;
			unsigned long MSTPD4 : 1;
			unsigned long MSTPD3 : 1;
			unsigned long MSTPD2 : 1;
			unsigned long MSTPD1 : 1;
			unsigned long MSTPD0 : 1;
#endif
	} BIT;
	} MSTPCRD;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long PCKD : 4;
			unsigned long PCKC : 4;
			unsigned long PCKB : 4;
			unsigned long PCKA : 4;
			unsigned long BCK : 4;
			unsigned long  : 2;
			unsigned long PSTOP0 : 1;
			unsigned long PSTOP1 : 1;
			unsigned long ICK : 4;
			unsigned long FCK : 4;
#else
			unsigned long FCK : 4;
			unsigned long ICK : 4;
			unsigned long PSTOP1 : 1;
			unsigned long PSTOP0 : 1;
			unsigned long  : 2;
			unsigned long BCK : 4;
			unsigned long PCKA : 4;
			unsigned long PCKB : 4;
			unsigned long PCKC : 4;
			unsigned long PCKD : 4;
#endif
	} BIT;
	} SCKCR;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 4;
			unsigned short UCK : 4;
			unsigned short  : 8;
#else
			unsigned short  : 8;
			unsigned short UCK : 4;
			unsigned short  : 4;
#endif
	} BIT;
	} SCKCR2;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 8;
			unsigned short CKSEL : 3;
			unsigned short  : 5;
#else
			unsigned short  : 5;
			unsigned short CKSEL : 3;
			unsigned short  : 8;
#endif
	} BIT;
	} SCKCR3;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PLIDIV : 2;
			unsigned short  : 2;
			unsigned short PLLSRCSEL : 1;
			unsigned short  : 3;
			unsigned short STC : 6;
			unsigned short  : 2;
#else
			unsigned short  : 2;
			unsigned short STC : 6;
			unsigned short  : 3;
			unsigned short PLLSRCSEL : 1;
			unsigned short  : 2;
			unsigned short PLIDIV : 2;
#endif
	} BIT;
	} PLLCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PLLEN : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char PLLEN : 1;
#endif
	} BIT;
	} PLLCR2;
	char           wk3[5];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char BCLKDIV : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char BCLKDIV : 1;
#endif
	} BIT;
	} BCKCR;
	char           wk4[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MOSTP : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char MOSTP : 1;
#endif
	} BIT;
	} MOSCCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SOSTP : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char SOSTP : 1;
#endif
	} BIT;
	} SOSCCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char LCSTP : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char LCSTP : 1;
#endif
	} BIT;
	} LOCOCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char ILCSTP : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char ILCSTP : 1;
#endif
	} BIT;
	} ILOCOCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char HCSTP : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char HCSTP : 1;
#endif
	} BIT;
	} HOCOCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char HCFRQ : 2;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char HCFRQ : 2;
#endif
	} BIT;
	} HOCOCR2;
	char           wk5[4];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MOOVF : 1;
			unsigned char SOOVF : 1;
			unsigned char PLOVF : 1;
			unsigned char HCOVF : 1;
			unsigned char ILCOVF : 1;
			unsigned char PPLOVF : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char PPLOVF : 1;
			unsigned char ILCOVF : 1;
			unsigned char HCOVF : 1;
			unsigned char PLOVF : 1;
			unsigned char SOOVF : 1;
			unsigned char MOOVF : 1;
#endif
	} BIT;
	} OSCOVFSR;
	char           wk6[1];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 8;
			unsigned short CKOSEL : 3;
			unsigned short  : 1;
			unsigned short CKODIV : 3;
			unsigned short CKOSTP : 1;
#else
			unsigned short CKOSTP : 1;
			unsigned short CKODIV : 3;
			unsigned short  : 1;
			unsigned short CKOSEL : 3;
			unsigned short  : 8;
#endif
	} BIT;
	} CKOCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char OSTDIE : 1;
			unsigned char  : 6;
			unsigned char OSTDE : 1;
#else
			unsigned char OSTDE : 1;
			unsigned char  : 6;
			unsigned char OSTDIE : 1;
#endif
	} BIT;
	} OSTDCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char OSTDF : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char OSTDF : 1;
#endif
	} BIT;
	} OSTDSR;
	char           wk7[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 4;
			unsigned short OUTCKSEL : 1;
			unsigned short  : 7;
			unsigned short UPLLSEL : 1;
			unsigned short  : 3;
#else
			unsigned short  : 3;
			unsigned short UPLLSEL : 1;
			unsigned short  : 7;
			unsigned short OUTCKSEL : 1;
			unsigned short  : 4;
#endif
	} BIT;
	} PACKCR;
	char           wk8[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PPLIDIV : 2;
			unsigned short  : 6;
			unsigned short PPLSTC : 6;
			unsigned short  : 2;
#else
			unsigned short  : 2;
			unsigned short PPLSTC : 6;
			unsigned short  : 6;
			unsigned short PPLIDIV : 2;
#endif
	} BIT;
	} PPLLCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PPLLEN : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char PPLLEN : 1;
#endif
	} BIT;
	} PPLLCR2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PPLCK : 4;
			unsigned char  : 4;
#else
			unsigned char  : 4;
			unsigned char PPLCK : 4;
#endif
	} BIT;
	} PPLLCR3;
	char           wk9[84];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char OPCM : 3;
			unsigned char  : 1;
			unsigned char OPCMTSF : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char OPCMTSF : 1;
			unsigned char  : 1;
			unsigned char OPCM : 3;
#endif
	} BIT;
	} OPCCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char RSTCKSEL : 3;
			unsigned char  : 4;
			unsigned char RSTCKEN : 1;
#else
			unsigned char RSTCKEN : 1;
			unsigned char  : 4;
			unsigned char RSTCKSEL : 3;
#endif
	} BIT;
	} RSTCKCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MSTS : 8;
#else
			unsigned char MSTS : 8;
#endif
	} BIT;
	} MOSCWTCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SSTS : 8;
#else
			unsigned char SSTS : 8;
#endif
	} BIT;
	} SOSCWTCR;
	char           wk10[28];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IWDTRF : 1;
			unsigned char WDTRF : 1;
			unsigned char SWRF : 1;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char SWRF : 1;
			unsigned char WDTRF : 1;
			unsigned char IWDTRF : 1;
#endif
	} BIT;
	} RSTSR2;
	char           wk11[1];
	unsigned short SWRR;
	char           wk12[28];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char LVD1IDTSEL : 2;
			unsigned char LVD1IRQSEL : 1;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char LVD1IRQSEL : 1;
			unsigned char LVD1IDTSEL : 2;
#endif
	} BIT;
	} LVD1CR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char LVD1DET : 1;
			unsigned char LVD1MON : 1;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char LVD1MON : 1;
			unsigned char LVD1DET : 1;
#endif
	} BIT;
	} LVD1SR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char LVD2IDTSEL : 2;
			unsigned char LVD2IRQSEL : 1;
			unsigned char  : 5;
#else
			unsigned char  : 5;
			unsigned char LVD2IRQSEL : 1;
			unsigned char LVD2IDTSEL : 2;
#endif
	} BIT;
	} LVD2CR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char LVD2DET : 1;
			unsigned char LVD2MON : 1;
			unsigned char  : 6;
#else
			unsigned char  : 6;
			unsigned char LVD2MON : 1;
			unsigned char LVD2DET : 1;
#endif
	} BIT;
	} LVD2SR;
	char           wk13[794];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PRC0 : 1;
			unsigned short PRC1 : 1;
			unsigned short  : 1;
			unsigned short PRC3 : 1;
			unsigned short  : 4;
			unsigned short PRKEY : 8;
#else
			unsigned short PRKEY : 8;
			unsigned short  : 4;
			unsigned short PRC3 : 1;
			unsigned short  : 1;
			unsigned short PRC1 : 1;
			unsigned short PRC0 : 1;
#endif
	} BIT;
	} PRCR;
	char           wk14[3100];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MEMWAIT : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char MEMWAIT : 1;
#endif
	} BIT;
	} MEMWAIT;
	char           wk15[45667];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DEEPCUT : 2;
			unsigned char  : 4;
			unsigned char IOKEEP : 1;
			unsigned char DPSBY : 1;
#else
			unsigned char DPSBY : 1;
			unsigned char IOKEEP : 1;
			unsigned char  : 4;
			unsigned char DEEPCUT : 2;
#endif
	} BIT;
	} DPSBYCR;
	char           wk16[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DIRQ0E : 1;
			unsigned char DIRQ1E : 1;
			unsigned char DIRQ2E : 1;
			unsigned char DIRQ3E : 1;
			unsigned char DIRQ4E : 1;
			unsigned char DIRQ5E : 1;
			unsigned char DIRQ6E : 1;
			unsigned char DIRQ7E : 1;
#else
			unsigned char DIRQ7E : 1;
			unsigned char DIRQ6E : 1;
			unsigned char DIRQ5E : 1;
			unsigned char DIRQ4E : 1;
			unsigned char DIRQ3E : 1;
			unsigned char DIRQ2E : 1;
			unsigned char DIRQ1E : 1;
			unsigned char DIRQ0E : 1;
#endif
	} BIT;
	} DPSIER0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DIRQ8E : 1;
			unsigned char DIRQ9E : 1;
			unsigned char DIRQ10E : 1;
			unsigned char DIRQ11E : 1;
			unsigned char DIRQ12E : 1;
			unsigned char DIRQ13E : 1;
			unsigned char DIRQ14E : 1;
			unsigned char DIRQ15E : 1;
#else
			unsigned char DIRQ15E : 1;
			unsigned char DIRQ14E : 1;
			unsigned char DIRQ13E : 1;
			unsigned char DIRQ12E : 1;
			unsigned char DIRQ11E : 1;
			unsigned char DIRQ10E : 1;
			unsigned char DIRQ9E : 1;
			unsigned char DIRQ8E : 1;
#endif
	} BIT;
	} DPSIER1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DLVD1IE : 1;
			unsigned char DLVD2IE : 1;
			unsigned char DRTCIIE : 1;
			unsigned char DRTCAIE : 1;
			unsigned char DNMIE : 1;
			unsigned char DRIICDIE : 1;
			unsigned char DRIICCIE : 1;
			unsigned char DUSBIE : 1;
#else
			unsigned char DUSBIE : 1;
			unsigned char DRIICCIE : 1;
			unsigned char DRIICDIE : 1;
			unsigned char DNMIE : 1;
			unsigned char DRTCAIE : 1;
			unsigned char DRTCIIE : 1;
			unsigned char DLVD2IE : 1;
			unsigned char DLVD1IE : 1;
#endif
	} BIT;
	} DPSIER2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DCANIE : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char DCANIE : 1;
#endif
	} BIT;
	} DPSIER3;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DIRQ0F : 1;
			unsigned char DIRQ1F : 1;
			unsigned char DIRQ2F : 1;
			unsigned char DIRQ3F : 1;
			unsigned char DIRQ4F : 1;
			unsigned char DIRQ5F : 1;
			unsigned char DIRQ6F : 1;
			unsigned char DIRQ7F : 1;
#else
			unsigned char DIRQ7F : 1;
			unsigned char DIRQ6F : 1;
			unsigned char DIRQ5F : 1;
			unsigned char DIRQ4F : 1;
			unsigned char DIRQ3F : 1;
			unsigned char DIRQ2F : 1;
			unsigned char DIRQ1F : 1;
			unsigned char DIRQ0F : 1;
#endif
	} BIT;
	} DPSIFR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DIRQ8F : 1;
			unsigned char DIRQ9F : 1;
			unsigned char DIRQ10F : 1;
			unsigned char DIRQ11F : 1;
			unsigned char DIRQ12F : 1;
			unsigned char DIRQ13F : 1;
			unsigned char DIRQ14F : 1;
			unsigned char DIRQ15F : 1;
#else
			unsigned char DIRQ15F : 1;
			unsigned char DIRQ14F : 1;
			unsigned char DIRQ13F : 1;
			unsigned char DIRQ12F : 1;
			unsigned char DIRQ11F : 1;
			unsigned char DIRQ10F : 1;
			unsigned char DIRQ9F : 1;
			unsigned char DIRQ8F : 1;
#endif
	} BIT;
	} DPSIFR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DLVD1IF : 1;
			unsigned char DLVD2IF : 1;
			unsigned char DRTCIIF : 1;
			unsigned char DRTCAIF : 1;
			unsigned char DNMIF : 1;
			unsigned char DRIICDIF : 1;
			unsigned char DRIICCIF : 1;
			unsigned char DUSBIF : 1;
#else
			unsigned char DUSBIF : 1;
			unsigned char DRIICCIF : 1;
			unsigned char DRIICDIF : 1;
			unsigned char DNMIF : 1;
			unsigned char DRTCAIF : 1;
			unsigned char DRTCIIF : 1;
			unsigned char DLVD2IF : 1;
			unsigned char DLVD1IF : 1;
#endif
	} BIT;
	} DPSIFR2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DCANIF : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char DCANIF : 1;
#endif
	} BIT;
	} DPSIFR3;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DIRQ0EG : 1;
			unsigned char DIRQ1EG : 1;
			unsigned char DIRQ2EG : 1;
			unsigned char DIRQ3EG : 1;
			unsigned char DIRQ4EG : 1;
			unsigned char DIRQ5EG : 1;
			unsigned char DIRQ6EG : 1;
			unsigned char DIRQ7EG : 1;
#else
			unsigned char DIRQ7EG : 1;
			unsigned char DIRQ6EG : 1;
			unsigned char DIRQ5EG : 1;
			unsigned char DIRQ4EG : 1;
			unsigned char DIRQ3EG : 1;
			unsigned char DIRQ2EG : 1;
			unsigned char DIRQ1EG : 1;
			unsigned char DIRQ0EG : 1;
#endif
	} BIT;
	} DPSIEGR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DIRQ8EG : 1;
			unsigned char DIRQ9EG : 1;
			unsigned char DIRQ10EG : 1;
			unsigned char DIRQ11EG : 1;
			unsigned char DIRQ12EG : 1;
			unsigned char DIRQ13EG : 1;
			unsigned char DIRQ14EG : 1;
			unsigned char DIRQ15EG : 1;
#else
			unsigned char DIRQ15EG : 1;
			unsigned char DIRQ14EG : 1;
			unsigned char DIRQ13EG : 1;
			unsigned char DIRQ12EG : 1;
			unsigned char DIRQ11EG : 1;
			unsigned char DIRQ10EG : 1;
			unsigned char DIRQ9EG : 1;
			unsigned char DIRQ8EG : 1;
#endif
	} BIT;
	} DPSIEGR1;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DLVD1EG : 1;
			unsigned char DLVD2EG : 1;
			unsigned char  : 2;
			unsigned char DNMIEG : 1;
			unsigned char DRIICDEG : 1;
			unsigned char DRIICCEG : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char DRIICCEG : 1;
			unsigned char DRIICDEG : 1;
			unsigned char DNMIEG : 1;
			unsigned char  : 2;
			unsigned char DLVD2EG : 1;
			unsigned char DLVD1EG : 1;
#endif
	} BIT;
	} DPSIEGR2;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char DCANIEG : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char DCANIEG : 1;
#endif
	} BIT;
	} DPSIEGR3;
	char           wk17[2];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char PORF : 1;
			unsigned char LVD0RF : 1;
			unsigned char LVD1RF : 1;
			unsigned char LVD2RF : 1;
			unsigned char  : 3;
			unsigned char DPSRSTF : 1;
#else
			unsigned char DPSRSTF : 1;
			unsigned char  : 3;
			unsigned char LVD2RF : 1;
			unsigned char LVD1RF : 1;
			unsigned char LVD0RF : 1;
			unsigned char PORF : 1;
#endif
	} BIT;
	} RSTSR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CWSF : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char CWSF : 1;
#endif
	} BIT;
	} RSTSR1;
	char           wk18[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MOFXIN : 1;
			unsigned char  : 3;
			unsigned char MODRV2 : 2;
			unsigned char MOSEL : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char MOSEL : 1;
			unsigned char MODRV2 : 2;
			unsigned char  : 3;
			unsigned char MOFXIN : 1;
#endif
	} BIT;
	} MOFCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char HOCOPCNT : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char HOCOPCNT : 1;
#endif
	} BIT;
	} HOCOPCR;
	char           wk19[2];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 5;
			unsigned char LVD1E : 1;
			unsigned char LVD2E : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char LVD2E : 1;
			unsigned char LVD1E : 1;
			unsigned char  : 5;
#endif
	} BIT;
	} LVCMPCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char LVD1LVL : 4;
			unsigned char LVD2LVL : 4;
#else
			unsigned char LVD2LVL : 4;
			unsigned char LVD1LVL : 4;
#endif
	} BIT;
	} LVDLVLR;
	char           wk20[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char LVD1RIE : 1;
			unsigned char LVD1DFDIS : 1;
			unsigned char LVD1CMPE : 1;
			unsigned char  : 1;
			unsigned char LVD1FSAMP : 2;
			unsigned char LVD1RI : 1;
			unsigned char LVD1RN : 1;
#else
			unsigned char LVD1RN : 1;
			unsigned char LVD1RI : 1;
			unsigned char LVD1FSAMP : 2;
			unsigned char  : 1;
			unsigned char LVD1CMPE : 1;
			unsigned char LVD1DFDIS : 1;
			unsigned char LVD1RIE : 1;
#endif
	} BIT;
	} LVD1CR0;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char LVD2RIE : 1;
			unsigned char LVD2DFDIS : 1;
			unsigned char LVD2CMPE : 1;
			unsigned char  : 1;
			unsigned char LVD2FSAMP : 2;
			unsigned char LVD2RI : 1;
			unsigned char LVD2RN : 1;
#else
			unsigned char LVD2RN : 1;
			unsigned char LVD2RI : 1;
			unsigned char LVD2FSAMP : 2;
			unsigned char  : 1;
			unsigned char LVD2CMPE : 1;
			unsigned char LVD2DFDIS : 1;
			unsigned char LVD2RIE : 1;
#endif
	} BIT;
	} LVD2CR0;
	char           wk21[4];
	unsigned char  DPSBKR[32];
} st_system_t;

typedef struct st_temps {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 4;
			unsigned char TSOE : 1;
			unsigned char  : 2;
			unsigned char TSEN : 1;
#else
			unsigned char TSEN : 1;
			unsigned char  : 2;
			unsigned char TSOE : 1;
			unsigned char  : 4;
#endif
	} BIT;
	} TSCR;
} st_temps_t;

typedef struct st_tmr0 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 3;
			unsigned char CCLR : 2;
			unsigned char OVIE : 1;
			unsigned char CMIEA : 1;
			unsigned char CMIEB : 1;
#else
			unsigned char CMIEB : 1;
			unsigned char CMIEA : 1;
			unsigned char OVIE : 1;
			unsigned char CCLR : 2;
			unsigned char  : 3;
#endif
	} BIT;
	} TCR;
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char OSA : 2;
			unsigned char OSB : 2;
			unsigned char ADTE : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char ADTE : 1;
			unsigned char OSB : 2;
			unsigned char OSA : 2;
#endif
	} BIT;
	} TCSR;
	char           wk1[1];
	unsigned char  TCORA;
	char           wk2[1];
	unsigned char  TCORB;
	char           wk3[1];
	unsigned char  TCNT;
	char           wk4[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CKS : 3;
			unsigned char CSS : 2;
			unsigned char  : 2;
			unsigned char TMRIS : 1;
#else
			unsigned char TMRIS : 1;
			unsigned char  : 2;
			unsigned char CSS : 2;
			unsigned char CKS : 3;
#endif
	} BIT;
	} TCCR;
	char           wk5[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TCS : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char TCS : 1;
#endif
	} BIT;
	} TCSTR;
} st_tmr0_t;

typedef struct st_tmr1 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 3;
			unsigned char CCLR : 2;
			unsigned char OVIE : 1;
			unsigned char CMIEA : 1;
			unsigned char CMIEB : 1;
#else
			unsigned char CMIEB : 1;
			unsigned char CMIEA : 1;
			unsigned char OVIE : 1;
			unsigned char CCLR : 2;
			unsigned char  : 3;
#endif
	} BIT;
	} TCR;
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char OSA : 2;
			unsigned char OSB : 2;
			unsigned char  : 4;
#else
			unsigned char  : 4;
			unsigned char OSB : 2;
			unsigned char OSA : 2;
#endif
	} BIT;
	} TCSR;
	char           wk1[1];
	unsigned char  TCORA;
	char           wk2[1];
	unsigned char  TCORB;
	char           wk3[1];
	unsigned char  TCNT;
	char           wk4[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CKS : 3;
			unsigned char CSS : 2;
			unsigned char  : 2;
			unsigned char TMRIS : 1;
#else
			unsigned char TMRIS : 1;
			unsigned char  : 2;
			unsigned char CSS : 2;
			unsigned char CKS : 3;
#endif
	} BIT;
	} TCCR;
	char           wk5[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TCS : 1;
			unsigned char  : 7;
#else
			unsigned char  : 7;
			unsigned char TCS : 1;
#endif
	} BIT;
	} TCSTR;
} st_tmr1_t;

typedef struct st_tmr01 {
	unsigned short TCORA;
	unsigned short TCORB;
	unsigned short TCNT;
	unsigned short TCCR;
} st_tmr01_t;

typedef struct st_tpu0 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFAEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFDEN : 1;
			unsigned char NFCS : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char NFCS : 2;
			unsigned char NFDEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFAEN : 1;
#endif
	} BIT;
	} NFCR;
	char           wk0[7];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC : 3;
			unsigned char CKEG : 2;
			unsigned char CCLR : 3;
#else
			unsigned char CCLR : 3;
			unsigned char CKEG : 2;
			unsigned char TPSC : 3;
#endif
	} BIT;
	} TCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MD : 4;
			unsigned char BFA : 1;
			unsigned char BFB : 1;
			unsigned char ICSELB : 1;
			unsigned char ICSELD : 1;
#else
			unsigned char ICSELD : 1;
			unsigned char ICSELB : 1;
			unsigned char BFB : 1;
			unsigned char BFA : 1;
			unsigned char MD : 4;
#endif
	} BIT;
	} TMDR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOA : 4;
			unsigned char IOB : 4;
#else
			unsigned char IOB : 4;
			unsigned char IOA : 4;
#endif
	} BIT;
	} TIORH;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOC : 4;
			unsigned char IOD : 4;
#else
			unsigned char IOD : 4;
			unsigned char IOC : 4;
#endif
	} BIT;
	} TIORL;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGIEA : 1;
			unsigned char TGIEB : 1;
			unsigned char TGIEC : 1;
			unsigned char TGIED : 1;
			unsigned char TCIEV : 1;
			unsigned char  : 2;
			unsigned char TTGE : 1;
#else
			unsigned char TTGE : 1;
			unsigned char  : 2;
			unsigned char TCIEV : 1;
			unsigned char TGIED : 1;
			unsigned char TGIEC : 1;
			unsigned char TGIEB : 1;
			unsigned char TGIEA : 1;
#endif
	} BIT;
	} TIER;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGFA : 1;
			unsigned char TGFB : 1;
			unsigned char TGFC : 1;
			unsigned char TGFD : 1;
			unsigned char TCFV : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char TCFV : 1;
			unsigned char TGFD : 1;
			unsigned char TGFC : 1;
			unsigned char TGFB : 1;
			unsigned char TGFA : 1;
#endif
	} BIT;
	} TSR;
	unsigned short TCNT;
	unsigned short TGRA;
	unsigned short TGRB;
	unsigned short TGRC;
	unsigned short TGRD;
} st_tpu0_t;

typedef struct st_tpu1 {
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFAEN : 1;
			unsigned char NFBEN : 1;
			unsigned char  : 2;
			unsigned char NFCS : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char NFCS : 2;
			unsigned char  : 2;
			unsigned char NFBEN : 1;
			unsigned char NFAEN : 1;
#endif
	} BIT;
	} NFCR;
	char           wk1[22];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC : 3;
			unsigned char CKEG : 2;
			unsigned char CCLR : 2;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char CCLR : 2;
			unsigned char CKEG : 2;
			unsigned char TPSC : 3;
#endif
	} BIT;
	} TCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MD : 4;
			unsigned char  : 2;
			unsigned char ICSELB : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ICSELB : 1;
			unsigned char  : 2;
			unsigned char MD : 4;
#endif
	} BIT;
	} TMDR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOA : 4;
			unsigned char IOB : 4;
#else
			unsigned char IOB : 4;
			unsigned char IOA : 4;
#endif
	} BIT;
	} TIOR;
	char           wk2[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGIEA : 1;
			unsigned char TGIEB : 1;
			unsigned char  : 2;
			unsigned char TCIEV : 1;
			unsigned char TCIEU : 1;
			unsigned char  : 1;
			unsigned char TTGE : 1;
#else
			unsigned char TTGE : 1;
			unsigned char  : 1;
			unsigned char TCIEU : 1;
			unsigned char TCIEV : 1;
			unsigned char  : 2;
			unsigned char TGIEB : 1;
			unsigned char TGIEA : 1;
#endif
	} BIT;
	} TIER;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGFA : 1;
			unsigned char TGFB : 1;
			unsigned char  : 2;
			unsigned char TCFV : 1;
			unsigned char TCFU : 1;
			unsigned char  : 1;
			unsigned char TCFD : 1;
#else
			unsigned char TCFD : 1;
			unsigned char  : 1;
			unsigned char TCFU : 1;
			unsigned char TCFV : 1;
			unsigned char  : 2;
			unsigned char TGFB : 1;
			unsigned char TGFA : 1;
#endif
	} BIT;
	} TSR;
	unsigned short TCNT;
	unsigned short TGRA;
	unsigned short TGRB;
} st_tpu1_t;

typedef struct st_tpu2 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFAEN : 1;
			unsigned char NFBEN : 1;
			unsigned char  : 2;
			unsigned char NFCS : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char NFCS : 2;
			unsigned char  : 2;
			unsigned char NFBEN : 1;
			unsigned char NFAEN : 1;
#endif
	} BIT;
	} NFCR;
	char           wk0[37];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC : 3;
			unsigned char CKEG : 2;
			unsigned char CCLR : 2;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char CCLR : 2;
			unsigned char CKEG : 2;
			unsigned char TPSC : 3;
#endif
	} BIT;
	} TCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MD : 4;
			unsigned char  : 2;
			unsigned char ICSELB : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ICSELB : 1;
			unsigned char  : 2;
			unsigned char MD : 4;
#endif
	} BIT;
	} TMDR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOA : 4;
			unsigned char IOB : 4;
#else
			unsigned char IOB : 4;
			unsigned char IOA : 4;
#endif
	} BIT;
	} TIOR;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGIEA : 1;
			unsigned char TGIEB : 1;
			unsigned char  : 2;
			unsigned char TCIEV : 1;
			unsigned char TCIEU : 1;
			unsigned char  : 1;
			unsigned char TTGE : 1;
#else
			unsigned char TTGE : 1;
			unsigned char  : 1;
			unsigned char TCIEU : 1;
			unsigned char TCIEV : 1;
			unsigned char  : 2;
			unsigned char TGIEB : 1;
			unsigned char TGIEA : 1;
#endif
	} BIT;
	} TIER;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGFA : 1;
			unsigned char TGFB : 1;
			unsigned char  : 2;
			unsigned char TCFV : 1;
			unsigned char TCFU : 1;
			unsigned char  : 1;
			unsigned char TCFD : 1;
#else
			unsigned char TCFD : 1;
			unsigned char  : 1;
			unsigned char TCFU : 1;
			unsigned char TCFV : 1;
			unsigned char  : 2;
			unsigned char TGFB : 1;
			unsigned char TGFA : 1;
#endif
	} BIT;
	} TSR;
	unsigned short TCNT;
	unsigned short TGRA;
	unsigned short TGRB;
} st_tpu2_t;

typedef struct st_tpu3 {
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFAEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFDEN : 1;
			unsigned char NFCS : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char NFCS : 2;
			unsigned char NFDEN : 1;
			unsigned char NFCEN : 1;
			unsigned char NFBEN : 1;
			unsigned char NFAEN : 1;
#endif
	} BIT;
	} NFCR;
	char           wk1[52];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC : 3;
			unsigned char CKEG : 2;
			unsigned char CCLR : 3;
#else
			unsigned char CCLR : 3;
			unsigned char CKEG : 2;
			unsigned char TPSC : 3;
#endif
	} BIT;
	} TCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MD : 4;
			unsigned char BFA : 1;
			unsigned char BFB : 1;
			unsigned char ICSELB : 1;
			unsigned char ICSELD : 1;
#else
			unsigned char ICSELD : 1;
			unsigned char ICSELB : 1;
			unsigned char BFB : 1;
			unsigned char BFA : 1;
			unsigned char MD : 4;
#endif
	} BIT;
	} TMDR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOA : 4;
			unsigned char IOB : 4;
#else
			unsigned char IOB : 4;
			unsigned char IOA : 4;
#endif
	} BIT;
	} TIORH;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOC : 4;
			unsigned char IOD : 4;
#else
			unsigned char IOD : 4;
			unsigned char IOC : 4;
#endif
	} BIT;
	} TIORL;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGIEA : 1;
			unsigned char TGIEB : 1;
			unsigned char TGIEC : 1;
			unsigned char TGIED : 1;
			unsigned char TCIEV : 1;
			unsigned char  : 2;
			unsigned char TTGE : 1;
#else
			unsigned char TTGE : 1;
			unsigned char  : 2;
			unsigned char TCIEV : 1;
			unsigned char TGIED : 1;
			unsigned char TGIEC : 1;
			unsigned char TGIEB : 1;
			unsigned char TGIEA : 1;
#endif
	} BIT;
	} TIER;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGFA : 1;
			unsigned char TGFB : 1;
			unsigned char TGFC : 1;
			unsigned char TGFD : 1;
			unsigned char TCFV : 1;
			unsigned char  : 3;
#else
			unsigned char  : 3;
			unsigned char TCFV : 1;
			unsigned char TGFD : 1;
			unsigned char TGFC : 1;
			unsigned char TGFB : 1;
			unsigned char TGFA : 1;
#endif
	} BIT;
	} TSR;
	unsigned short TCNT;
	unsigned short TGRA;
	unsigned short TGRB;
	unsigned short TGRC;
	unsigned short TGRD;
} st_tpu3_t;

typedef struct st_tpu4 {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFAEN : 1;
			unsigned char NFBEN : 1;
			unsigned char  : 2;
			unsigned char NFCS : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char NFCS : 2;
			unsigned char  : 2;
			unsigned char NFBEN : 1;
			unsigned char NFAEN : 1;
#endif
	} BIT;
	} NFCR;
	char           wk0[67];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC : 3;
			unsigned char CKEG : 2;
			unsigned char CCLR : 2;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char CCLR : 2;
			unsigned char CKEG : 2;
			unsigned char TPSC : 3;
#endif
	} BIT;
	} TCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MD : 4;
			unsigned char  : 2;
			unsigned char ICSELB : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ICSELB : 1;
			unsigned char  : 2;
			unsigned char MD : 4;
#endif
	} BIT;
	} TMDR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOA : 4;
			unsigned char IOB : 4;
#else
			unsigned char IOB : 4;
			unsigned char IOA : 4;
#endif
	} BIT;
	} TIOR;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGIEA : 1;
			unsigned char TGIEB : 1;
			unsigned char  : 2;
			unsigned char TCIEV : 1;
			unsigned char TCIEU : 1;
			unsigned char  : 1;
			unsigned char TTGE : 1;
#else
			unsigned char TTGE : 1;
			unsigned char  : 1;
			unsigned char TCIEU : 1;
			unsigned char TCIEV : 1;
			unsigned char  : 2;
			unsigned char TGIEB : 1;
			unsigned char TGIEA : 1;
#endif
	} BIT;
	} TIER;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGFA : 1;
			unsigned char TGFB : 1;
			unsigned char  : 2;
			unsigned char TCFV : 1;
			unsigned char TCFU : 1;
			unsigned char  : 1;
			unsigned char TCFD : 1;
#else
			unsigned char TCFD : 1;
			unsigned char  : 1;
			unsigned char TCFU : 1;
			unsigned char TCFV : 1;
			unsigned char  : 2;
			unsigned char TGFB : 1;
			unsigned char TGFA : 1;
#endif
	} BIT;
	} TSR;
	unsigned short TCNT;
	unsigned short TGRA;
	unsigned short TGRB;
} st_tpu4_t;

typedef struct st_tpu5 {
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char NFAEN : 1;
			unsigned char NFBEN : 1;
			unsigned char  : 2;
			unsigned char NFCS : 2;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char NFCS : 2;
			unsigned char  : 2;
			unsigned char NFBEN : 1;
			unsigned char NFAEN : 1;
#endif
	} BIT;
	} NFCR;
	char           wk1[82];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TPSC : 3;
			unsigned char CKEG : 2;
			unsigned char CCLR : 2;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char CCLR : 2;
			unsigned char CKEG : 2;
			unsigned char TPSC : 3;
#endif
	} BIT;
	} TCR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char MD : 4;
			unsigned char  : 2;
			unsigned char ICSELB : 1;
			unsigned char  : 1;
#else
			unsigned char  : 1;
			unsigned char ICSELB : 1;
			unsigned char  : 2;
			unsigned char MD : 4;
#endif
	} BIT;
	} TMDR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char IOA : 4;
			unsigned char IOB : 4;
#else
			unsigned char IOB : 4;
			unsigned char IOA : 4;
#endif
	} BIT;
	} TIOR;
	char           wk2[1];
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGIEA : 1;
			unsigned char TGIEB : 1;
			unsigned char  : 2;
			unsigned char TCIEV : 1;
			unsigned char TCIEU : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char TCIEU : 1;
			unsigned char TCIEV : 1;
			unsigned char  : 2;
			unsigned char TGIEB : 1;
			unsigned char TGIEA : 1;
#endif
	} BIT;
	} TIER;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char TGFA : 1;
			unsigned char TGFB : 1;
			unsigned char  : 2;
			unsigned char TCFV : 1;
			unsigned char TCFU : 1;
			unsigned char  : 1;
			unsigned char TCFD : 1;
#else
			unsigned char TCFD : 1;
			unsigned char  : 1;
			unsigned char TCFU : 1;
			unsigned char TCFV : 1;
			unsigned char  : 2;
			unsigned char TGFB : 1;
			unsigned char TGFA : 1;
#endif
	} BIT;
	} TSR;
	unsigned short TCNT;
	unsigned short TGRA;
	unsigned short TGRB;
} st_tpu5_t;

typedef struct st_tpua {
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char CST0 : 1;
			unsigned char CST1 : 1;
			unsigned char CST2 : 1;
			unsigned char CST3 : 1;
			unsigned char CST4 : 1;
			unsigned char CST5 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char CST5 : 1;
			unsigned char CST4 : 1;
			unsigned char CST3 : 1;
			unsigned char CST2 : 1;
			unsigned char CST1 : 1;
			unsigned char CST0 : 1;
#endif
	} BIT;
	} TSTR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char SYNC0 : 1;
			unsigned char SYNC1 : 1;
			unsigned char SYNC2 : 1;
			unsigned char SYNC3 : 1;
			unsigned char SYNC4 : 1;
			unsigned char SYNC5 : 1;
			unsigned char  : 2;
#else
			unsigned char  : 2;
			unsigned char SYNC5 : 1;
			unsigned char SYNC4 : 1;
			unsigned char SYNC3 : 1;
			unsigned char SYNC2 : 1;
			unsigned char SYNC1 : 1;
			unsigned char SYNC0 : 1;
#endif
	} BIT;
	} TSYR;
} st_tpua_t;

typedef struct st_usb {
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long SRPC0 : 1;
			unsigned long RPUE0 : 1;
			unsigned long  : 1;
			unsigned long DRPD0 : 1;
			unsigned long FIXPHY0 : 1;
			unsigned long  : 11;
			unsigned long DP0 : 1;
			unsigned long DM0 : 1;
			unsigned long  : 2;
			unsigned long DOVCA0 : 1;
			unsigned long DOVCB0 : 1;
			unsigned long  : 1;
			unsigned long DVBSTS0 : 1;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long DVBSTS0 : 1;
			unsigned long  : 1;
			unsigned long DOVCB0 : 1;
			unsigned long DOVCA0 : 1;
			unsigned long  : 2;
			unsigned long DM0 : 1;
			unsigned long DP0 : 1;
			unsigned long  : 11;
			unsigned long FIXPHY0 : 1;
			unsigned long DRPD0 : 1;
			unsigned long  : 1;
			unsigned long RPUE0 : 1;
			unsigned long SRPC0 : 1;
#endif
	} BIT;
	} DPUSR0R;
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long DPINTE0 : 1;
			unsigned long DMINTE0 : 1;
			unsigned long  : 2;
			unsigned long DOVRCRAE0 : 1;
			unsigned long DOVRCRBE0 : 1;
			unsigned long  : 1;
			unsigned long DVBSE0 : 1;
			unsigned long  : 8;
			unsigned long DPINT0 : 1;
			unsigned long DMINT0 : 1;
			unsigned long  : 2;
			unsigned long DOVRCRA0 : 1;
			unsigned long DOVRCRB0 : 1;
			unsigned long  : 1;
			unsigned long DVBINT0 : 1;
			unsigned long  : 8;
#else
			unsigned long  : 8;
			unsigned long DVBINT0 : 1;
			unsigned long  : 1;
			unsigned long DOVRCRB0 : 1;
			unsigned long DOVRCRA0 : 1;
			unsigned long  : 2;
			unsigned long DMINT0 : 1;
			unsigned long DPINT0 : 1;
			unsigned long  : 8;
			unsigned long DVBSE0 : 1;
			unsigned long  : 1;
			unsigned long DOVRCRBE0 : 1;
			unsigned long DOVRCRAE0 : 1;
			unsigned long  : 2;
			unsigned long DMINTE0 : 1;
			unsigned long DPINTE0 : 1;
#endif
	} BIT;
	} DPUSR1R;
} st_usb_t;

typedef struct st_usb0 {
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short USBE : 1;
			unsigned short  : 3;
			unsigned short DPRPU : 1;
			unsigned short DRPD : 1;
			unsigned short DCFM : 1;
			unsigned short  : 3;
			unsigned short SCKE : 1;
			unsigned short  : 5;
#else
			unsigned short  : 5;
			unsigned short SCKE : 1;
			unsigned short  : 3;
			unsigned short DCFM : 1;
			unsigned short DRPD : 1;
			unsigned short DPRPU : 1;
			unsigned short  : 3;
			unsigned short USBE : 1;
#endif
	} BIT;
	} SYSCFG;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short LNST : 2;
			unsigned short IDMON : 1;
			unsigned short  : 2;
			unsigned short SOFEA : 1;
			unsigned short HTACT : 1;
			unsigned short  : 7;
			unsigned short OVCMON : 2;
#else
			unsigned short OVCMON : 2;
			unsigned short  : 7;
			unsigned short HTACT : 1;
			unsigned short SOFEA : 1;
			unsigned short  : 2;
			unsigned short IDMON : 1;
			unsigned short LNST : 2;
#endif
	} BIT;
	} SYSSTS0;
	char           wk1[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short RHST : 3;
			unsigned short  : 1;
			unsigned short UACT : 1;
			unsigned short RESUME : 1;
			unsigned short USBRST : 1;
			unsigned short RWUPE : 1;
			unsigned short WKUP : 1;
			unsigned short VBUSEN : 1;
			unsigned short EXICEN : 1;
			unsigned short HNPBTOA : 1;
			unsigned short  : 4;
#else
			unsigned short  : 4;
			unsigned short HNPBTOA : 1;
			unsigned short EXICEN : 1;
			unsigned short VBUSEN : 1;
			unsigned short WKUP : 1;
			unsigned short RWUPE : 1;
			unsigned short USBRST : 1;
			unsigned short RESUME : 1;
			unsigned short UACT : 1;
			unsigned short  : 1;
			unsigned short RHST : 3;
#endif
	} BIT;
	} DVSTCTR0;
	char           wk2[10];
	union {
		unsigned short WORD;
		struct {
			unsigned char L;
			unsigned char H;
		} BYTE;
	} CFIFO;
	char           wk3[2];
	union {
		unsigned short WORD;
		struct {
			unsigned char L;
			unsigned char H;
		} BYTE;
	} D0FIFO;
	char           wk4[2];
	union {
		unsigned short WORD;
		struct {
			unsigned char L;
			unsigned char H;
		} BYTE;
	} D1FIFO;
	char           wk5[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CURPIPE : 4;
			unsigned short  : 1;
			unsigned short ISEL : 1;
			unsigned short  : 2;
			unsigned short BIGEND : 1;
			unsigned short  : 1;
			unsigned short MBW : 1;
			unsigned short  : 3;
			unsigned short REW : 1;
			unsigned short RCNT : 1;
#else
			unsigned short RCNT : 1;
			unsigned short REW : 1;
			unsigned short  : 3;
			unsigned short MBW : 1;
			unsigned short  : 1;
			unsigned short BIGEND : 1;
			unsigned short  : 2;
			unsigned short ISEL : 1;
			unsigned short  : 1;
			unsigned short CURPIPE : 4;
#endif
	} BIT;
	} CFIFOSEL;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short DTLN : 9;
			unsigned short  : 4;
			unsigned short FRDY : 1;
			unsigned short BCLR : 1;
			unsigned short BVAL : 1;
#else
			unsigned short BVAL : 1;
			unsigned short BCLR : 1;
			unsigned short FRDY : 1;
			unsigned short  : 4;
			unsigned short DTLN : 9;
#endif
	} BIT;
	} CFIFOCTR;
	char           wk6[4];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CURPIPE : 4;
			unsigned short  : 4;
			unsigned short BIGEND : 1;
			unsigned short  : 1;
			unsigned short MBW : 1;
			unsigned short  : 1;
			unsigned short DREQE : 1;
			unsigned short DCLRM : 1;
			unsigned short REW : 1;
			unsigned short RCNT : 1;
#else
			unsigned short RCNT : 1;
			unsigned short REW : 1;
			unsigned short DCLRM : 1;
			unsigned short DREQE : 1;
			unsigned short  : 1;
			unsigned short MBW : 1;
			unsigned short  : 1;
			unsigned short BIGEND : 1;
			unsigned short  : 4;
			unsigned short CURPIPE : 4;
#endif
	} BIT;
	} D0FIFOSEL;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short DTLN : 9;
			unsigned short  : 4;
			unsigned short FRDY : 1;
			unsigned short BCLR : 1;
			unsigned short BVAL : 1;
#else
			unsigned short BVAL : 1;
			unsigned short BCLR : 1;
			unsigned short FRDY : 1;
			unsigned short  : 4;
			unsigned short DTLN : 9;
#endif
	} BIT;
	} D0FIFOCTR;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CURPIPE : 4;
			unsigned short  : 4;
			unsigned short BIGEND : 1;
			unsigned short  : 1;
			unsigned short MBW : 1;
			unsigned short  : 1;
			unsigned short DREQE : 1;
			unsigned short DCLRM : 1;
			unsigned short REW : 1;
			unsigned short RCNT : 1;
#else
			unsigned short RCNT : 1;
			unsigned short REW : 1;
			unsigned short DCLRM : 1;
			unsigned short DREQE : 1;
			unsigned short  : 1;
			unsigned short MBW : 1;
			unsigned short  : 1;
			unsigned short BIGEND : 1;
			unsigned short  : 4;
			unsigned short CURPIPE : 4;
#endif
	} BIT;
	} D1FIFOSEL;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short DTLN : 9;
			unsigned short  : 4;
			unsigned short FRDY : 1;
			unsigned short BCLR : 1;
			unsigned short BVAL : 1;
#else
			unsigned short BVAL : 1;
			unsigned short BCLR : 1;
			unsigned short FRDY : 1;
			unsigned short  : 4;
			unsigned short DTLN : 9;
#endif
	} BIT;
	} D1FIFOCTR;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 8;
			unsigned short BRDYE : 1;
			unsigned short NRDYE : 1;
			unsigned short BEMPE : 1;
			unsigned short CTRE : 1;
			unsigned short DVSE : 1;
			unsigned short SOFE : 1;
			unsigned short RSME : 1;
			unsigned short VBSE : 1;
#else
			unsigned short VBSE : 1;
			unsigned short RSME : 1;
			unsigned short SOFE : 1;
			unsigned short DVSE : 1;
			unsigned short CTRE : 1;
			unsigned short BEMPE : 1;
			unsigned short NRDYE : 1;
			unsigned short BRDYE : 1;
			unsigned short  : 8;
#endif
	} BIT;
	} INTENB0;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 4;
			unsigned short SACKE : 1;
			unsigned short SIGNE : 1;
			unsigned short EOFERRE : 1;
			unsigned short  : 4;
			unsigned short ATTCHE : 1;
			unsigned short DTCHE : 1;
			unsigned short  : 1;
			unsigned short BCHGE : 1;
			unsigned short OVRCRE : 1;
#else
			unsigned short OVRCRE : 1;
			unsigned short BCHGE : 1;
			unsigned short  : 1;
			unsigned short DTCHE : 1;
			unsigned short ATTCHE : 1;
			unsigned short  : 4;
			unsigned short EOFERRE : 1;
			unsigned short SIGNE : 1;
			unsigned short SACKE : 1;
			unsigned short  : 4;
#endif
	} BIT;
	} INTENB1;
	char           wk7[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PIPE0BRDYE : 1;
			unsigned short PIPE1BRDYE : 1;
			unsigned short PIPE2BRDYE : 1;
			unsigned short PIPE3BRDYE : 1;
			unsigned short PIPE4BRDYE : 1;
			unsigned short PIPE5BRDYE : 1;
			unsigned short PIPE6BRDYE : 1;
			unsigned short PIPE7BRDYE : 1;
			unsigned short PIPE8BRDYE : 1;
			unsigned short PIPE9BRDYE : 1;
			unsigned short  : 6;
#else
			unsigned short  : 6;
			unsigned short PIPE9BRDYE : 1;
			unsigned short PIPE8BRDYE : 1;
			unsigned short PIPE7BRDYE : 1;
			unsigned short PIPE6BRDYE : 1;
			unsigned short PIPE5BRDYE : 1;
			unsigned short PIPE4BRDYE : 1;
			unsigned short PIPE3BRDYE : 1;
			unsigned short PIPE2BRDYE : 1;
			unsigned short PIPE1BRDYE : 1;
			unsigned short PIPE0BRDYE : 1;
#endif
	} BIT;
	} BRDYENB;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PIPE0NRDYE : 1;
			unsigned short PIPE1NRDYE : 1;
			unsigned short PIPE2NRDYE : 1;
			unsigned short PIPE3NRDYE : 1;
			unsigned short PIPE4NRDYE : 1;
			unsigned short PIPE5NRDYE : 1;
			unsigned short PIPE6NRDYE : 1;
			unsigned short PIPE7NRDYE : 1;
			unsigned short PIPE8NRDYE : 1;
			unsigned short PIPE9NRDYE : 1;
			unsigned short  : 6;
#else
			unsigned short  : 6;
			unsigned short PIPE9NRDYE : 1;
			unsigned short PIPE8NRDYE : 1;
			unsigned short PIPE7NRDYE : 1;
			unsigned short PIPE6NRDYE : 1;
			unsigned short PIPE5NRDYE : 1;
			unsigned short PIPE4NRDYE : 1;
			unsigned short PIPE3NRDYE : 1;
			unsigned short PIPE2NRDYE : 1;
			unsigned short PIPE1NRDYE : 1;
			unsigned short PIPE0NRDYE : 1;
#endif
	} BIT;
	} NRDYENB;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PIPE0BEMPE : 1;
			unsigned short PIPE1BEMPE : 1;
			unsigned short PIPE2BEMPE : 1;
			unsigned short PIPE3BEMPE : 1;
			unsigned short PIPE4BEMPE : 1;
			unsigned short PIPE5BEMPE : 1;
			unsigned short PIPE6BEMPE : 1;
			unsigned short PIPE7BEMPE : 1;
			unsigned short PIPE8BEMPE : 1;
			unsigned short PIPE9BEMPE : 1;
			unsigned short  : 6;
#else
			unsigned short  : 6;
			unsigned short PIPE9BEMPE : 1;
			unsigned short PIPE8BEMPE : 1;
			unsigned short PIPE7BEMPE : 1;
			unsigned short PIPE6BEMPE : 1;
			unsigned short PIPE5BEMPE : 1;
			unsigned short PIPE4BEMPE : 1;
			unsigned short PIPE3BEMPE : 1;
			unsigned short PIPE2BEMPE : 1;
			unsigned short PIPE1BEMPE : 1;
			unsigned short PIPE0BEMPE : 1;
#endif
	} BIT;
	} BEMPENB;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 4;
			unsigned short EDGESTS : 1;
			unsigned short  : 1;
			unsigned short BRDYM : 1;
			unsigned short  : 1;
			unsigned short TRNENSEL : 1;
			unsigned short  : 7;
#else
			unsigned short  : 7;
			unsigned short TRNENSEL : 1;
			unsigned short  : 1;
			unsigned short BRDYM : 1;
			unsigned short  : 1;
			unsigned short EDGESTS : 1;
			unsigned short  : 4;
#endif
	} BIT;
	} SOFCFG;
	char           wk8[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CTSQ : 3;
			unsigned short VALID : 1;
			unsigned short DVSQ : 3;
			unsigned short VBSTS : 1;
			unsigned short BRDY : 1;
			unsigned short NRDY : 1;
			unsigned short BEMP : 1;
			unsigned short CTRT : 1;
			unsigned short DVST : 1;
			unsigned short SOFR : 1;
			unsigned short RESM : 1;
			unsigned short VBINT : 1;
#else
			unsigned short VBINT : 1;
			unsigned short RESM : 1;
			unsigned short SOFR : 1;
			unsigned short DVST : 1;
			unsigned short CTRT : 1;
			unsigned short BEMP : 1;
			unsigned short NRDY : 1;
			unsigned short BRDY : 1;
			unsigned short VBSTS : 1;
			unsigned short DVSQ : 3;
			unsigned short VALID : 1;
			unsigned short CTSQ : 3;
#endif
	} BIT;
	} INTSTS0;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 4;
			unsigned short SACK : 1;
			unsigned short SIGN : 1;
			unsigned short EOFERR : 1;
			unsigned short  : 4;
			unsigned short ATTCH : 1;
			unsigned short DTCH : 1;
			unsigned short  : 1;
			unsigned short BCHG : 1;
			unsigned short OVRCR : 1;
#else
			unsigned short OVRCR : 1;
			unsigned short BCHG : 1;
			unsigned short  : 1;
			unsigned short DTCH : 1;
			unsigned short ATTCH : 1;
			unsigned short  : 4;
			unsigned short EOFERR : 1;
			unsigned short SIGN : 1;
			unsigned short SACK : 1;
			unsigned short  : 4;
#endif
	} BIT;
	} INTSTS1;
	char           wk9[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PIPE0BRDY : 1;
			unsigned short PIPE1BRDY : 1;
			unsigned short PIPE2BRDY : 1;
			unsigned short PIPE3BRDY : 1;
			unsigned short PIPE4BRDY : 1;
			unsigned short PIPE5BRDY : 1;
			unsigned short PIPE6BRDY : 1;
			unsigned short PIPE7BRDY : 1;
			unsigned short PIPE8BRDY : 1;
			unsigned short PIPE9BRDY : 1;
			unsigned short  : 6;
#else
			unsigned short  : 6;
			unsigned short PIPE9BRDY : 1;
			unsigned short PIPE8BRDY : 1;
			unsigned short PIPE7BRDY : 1;
			unsigned short PIPE6BRDY : 1;
			unsigned short PIPE5BRDY : 1;
			unsigned short PIPE4BRDY : 1;
			unsigned short PIPE3BRDY : 1;
			unsigned short PIPE2BRDY : 1;
			unsigned short PIPE1BRDY : 1;
			unsigned short PIPE0BRDY : 1;
#endif
	} BIT;
	} BRDYSTS;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PIPE0NRDY : 1;
			unsigned short PIPE1NRDY : 1;
			unsigned short PIPE2NRDY : 1;
			unsigned short PIPE3NRDY : 1;
			unsigned short PIPE4NRDY : 1;
			unsigned short PIPE5NRDY : 1;
			unsigned short PIPE6NRDY : 1;
			unsigned short PIPE7NRDY : 1;
			unsigned short PIPE8NRDY : 1;
			unsigned short PIPE9NRDY : 1;
			unsigned short  : 6;
#else
			unsigned short  : 6;
			unsigned short PIPE9NRDY : 1;
			unsigned short PIPE8NRDY : 1;
			unsigned short PIPE7NRDY : 1;
			unsigned short PIPE6NRDY : 1;
			unsigned short PIPE5NRDY : 1;
			unsigned short PIPE4NRDY : 1;
			unsigned short PIPE3NRDY : 1;
			unsigned short PIPE2NRDY : 1;
			unsigned short PIPE1NRDY : 1;
			unsigned short PIPE0NRDY : 1;
#endif
	} BIT;
	} NRDYSTS;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PIPE0BEMP : 1;
			unsigned short PIPE1BEMP : 1;
			unsigned short PIPE2BEMP : 1;
			unsigned short PIPE3BEMP : 1;
			unsigned short PIPE4BEMP : 1;
			unsigned short PIPE5BEMP : 1;
			unsigned short PIPE6BEMP : 1;
			unsigned short PIPE7BEMP : 1;
			unsigned short PIPE8BEMP : 1;
			unsigned short PIPE9BEMP : 1;
			unsigned short  : 6;
#else
			unsigned short  : 6;
			unsigned short PIPE9BEMP : 1;
			unsigned short PIPE8BEMP : 1;
			unsigned short PIPE7BEMP : 1;
			unsigned short PIPE6BEMP : 1;
			unsigned short PIPE5BEMP : 1;
			unsigned short PIPE4BEMP : 1;
			unsigned short PIPE3BEMP : 1;
			unsigned short PIPE2BEMP : 1;
			unsigned short PIPE1BEMP : 1;
			unsigned short PIPE0BEMP : 1;
#endif
	} BIT;
	} BEMPSTS;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short FRNM : 11;
			unsigned short  : 3;
			unsigned short CRCE : 1;
			unsigned short OVRN : 1;
#else
			unsigned short OVRN : 1;
			unsigned short CRCE : 1;
			unsigned short  : 3;
			unsigned short FRNM : 11;
#endif
	} BIT;
	} FRMNUM;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 15;
			unsigned short DVCHG : 1;
#else
			unsigned short DVCHG : 1;
			unsigned short  : 15;
#endif
	} BIT;
	} DVCHGR;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short USBADDR : 7;
			unsigned short  : 1;
			unsigned short STSRECOV : 4;
			unsigned short  : 4;
#else
			unsigned short  : 4;
			unsigned short STSRECOV : 4;
			unsigned short  : 1;
			unsigned short USBADDR : 7;
#endif
	} BIT;
	} USBADDR;
	char           wk10[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short BMREQUESTTYPE : 8;
			unsigned short BREQUEST : 8;
#else
			unsigned short BREQUEST : 8;
			unsigned short BMREQUESTTYPE : 8;
#endif
	} BIT;
	} USBREQ;
	unsigned short USBVAL;
	unsigned short USBINDX;
	unsigned short USBLENG;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 4;
			unsigned short DIR : 1;
			unsigned short  : 2;
			unsigned short SHTNAK : 1;
			unsigned short  : 8;
#else
			unsigned short  : 8;
			unsigned short SHTNAK : 1;
			unsigned short  : 2;
			unsigned short DIR : 1;
			unsigned short  : 4;
#endif
	} BIT;
	} DCPCFG;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short MXPS : 7;
			unsigned short  : 5;
			unsigned short DEVSEL : 4;
#else
			unsigned short DEVSEL : 4;
			unsigned short  : 5;
			unsigned short MXPS : 7;
#endif
	} BIT;
	} DCPMAXP;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PID : 2;
			unsigned short CCPL : 1;
			unsigned short  : 2;
			unsigned short PBUSY : 1;
			unsigned short SQMON : 1;
			unsigned short SQSET : 1;
			unsigned short SQCLR : 1;
			unsigned short  : 2;
			unsigned short SUREQCLR : 1;
			unsigned short  : 2;
			unsigned short SUREQ : 1;
			unsigned short BSTS : 1;
#else
			unsigned short BSTS : 1;
			unsigned short SUREQ : 1;
			unsigned short  : 2;
			unsigned short SUREQCLR : 1;
			unsigned short  : 2;
			unsigned short SQCLR : 1;
			unsigned short SQSET : 1;
			unsigned short SQMON : 1;
			unsigned short PBUSY : 1;
			unsigned short  : 2;
			unsigned short CCPL : 1;
			unsigned short PID : 2;
#endif
	} BIT;
	} DCPCTR;
	char           wk11[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PIPESEL : 4;
			unsigned short  : 12;
#else
			unsigned short  : 12;
			unsigned short PIPESEL : 4;
#endif
	} BIT;
	} PIPESEL;
	char           wk12[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short EPNUM : 4;
			unsigned short DIR : 1;
			unsigned short  : 2;
			unsigned short SHTNAK : 1;
			unsigned short  : 1;
			unsigned short DBLB : 1;
			unsigned short BFRE : 1;
			unsigned short  : 3;
			unsigned short TYPE : 2;
#else
			unsigned short TYPE : 2;
			unsigned short  : 3;
			unsigned short BFRE : 1;
			unsigned short DBLB : 1;
			unsigned short  : 1;
			unsigned short SHTNAK : 1;
			unsigned short  : 2;
			unsigned short DIR : 1;
			unsigned short EPNUM : 4;
#endif
	} BIT;
	} PIPECFG;
	char           wk13[2];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short MXPS : 9;
			unsigned short  : 3;
			unsigned short DEVSEL : 4;
#else
			unsigned short DEVSEL : 4;
			unsigned short  : 3;
			unsigned short MXPS : 9;
#endif
	} BIT;
	} PIPEMAXP;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short IITV : 3;
			unsigned short  : 9;
			unsigned short IFIS : 1;
			unsigned short  : 3;
#else
			unsigned short  : 3;
			unsigned short IFIS : 1;
			unsigned short  : 9;
			unsigned short IITV : 3;
#endif
	} BIT;
	} PIPEPERI;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PID : 2;
			unsigned short  : 3;
			unsigned short PBUSY : 1;
			unsigned short SQMON : 1;
			unsigned short SQSET : 1;
			unsigned short SQCLR : 1;
			unsigned short ACLRM : 1;
			unsigned short ATREPM : 1;
			unsigned short  : 3;
			unsigned short INBUFM : 1;
			unsigned short BSTS : 1;
#else
			unsigned short BSTS : 1;
			unsigned short INBUFM : 1;
			unsigned short  : 3;
			unsigned short ATREPM : 1;
			unsigned short ACLRM : 1;
			unsigned short SQCLR : 1;
			unsigned short SQSET : 1;
			unsigned short SQMON : 1;
			unsigned short PBUSY : 1;
			unsigned short  : 3;
			unsigned short PID : 2;
#endif
	} BIT;
	} PIPE1CTR;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PID : 2;
			unsigned short  : 3;
			unsigned short PBUSY : 1;
			unsigned short SQMON : 1;
			unsigned short SQSET : 1;
			unsigned short SQCLR : 1;
			unsigned short ACLRM : 1;
			unsigned short ATREPM : 1;
			unsigned short  : 3;
			unsigned short INBUFM : 1;
			unsigned short BSTS : 1;
#else
			unsigned short BSTS : 1;
			unsigned short INBUFM : 1;
			unsigned short  : 3;
			unsigned short ATREPM : 1;
			unsigned short ACLRM : 1;
			unsigned short SQCLR : 1;
			unsigned short SQSET : 1;
			unsigned short SQMON : 1;
			unsigned short PBUSY : 1;
			unsigned short  : 3;
			unsigned short PID : 2;
#endif
	} BIT;
	} PIPE2CTR;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PID : 2;
			unsigned short  : 3;
			unsigned short PBUSY : 1;
			unsigned short SQMON : 1;
			unsigned short SQSET : 1;
			unsigned short SQCLR : 1;
			unsigned short ACLRM : 1;
			unsigned short ATREPM : 1;
			unsigned short  : 3;
			unsigned short INBUFM : 1;
			unsigned short BSTS : 1;
#else
			unsigned short BSTS : 1;
			unsigned short INBUFM : 1;
			unsigned short  : 3;
			unsigned short ATREPM : 1;
			unsigned short ACLRM : 1;
			unsigned short SQCLR : 1;
			unsigned short SQSET : 1;
			unsigned short SQMON : 1;
			unsigned short PBUSY : 1;
			unsigned short  : 3;
			unsigned short PID : 2;
#endif
	} BIT;
	} PIPE3CTR;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PID : 2;
			unsigned short  : 3;
			unsigned short PBUSY : 1;
			unsigned short SQMON : 1;
			unsigned short SQSET : 1;
			unsigned short SQCLR : 1;
			unsigned short ACLRM : 1;
			unsigned short ATREPM : 1;
			unsigned short  : 3;
			unsigned short INBUFM : 1;
			unsigned short BSTS : 1;
#else
			unsigned short BSTS : 1;
			unsigned short INBUFM : 1;
			unsigned short  : 3;
			unsigned short ATREPM : 1;
			unsigned short ACLRM : 1;
			unsigned short SQCLR : 1;
			unsigned short SQSET : 1;
			unsigned short SQMON : 1;
			unsigned short PBUSY : 1;
			unsigned short  : 3;
			unsigned short PID : 2;
#endif
	} BIT;
	} PIPE4CTR;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PID : 2;
			unsigned short  : 3;
			unsigned short PBUSY : 1;
			unsigned short SQMON : 1;
			unsigned short SQSET : 1;
			unsigned short SQCLR : 1;
			unsigned short ACLRM : 1;
			unsigned short ATREPM : 1;
			unsigned short  : 3;
			unsigned short INBUFM : 1;
			unsigned short BSTS : 1;
#else
			unsigned short BSTS : 1;
			unsigned short INBUFM : 1;
			unsigned short  : 3;
			unsigned short ATREPM : 1;
			unsigned short ACLRM : 1;
			unsigned short SQCLR : 1;
			unsigned short SQSET : 1;
			unsigned short SQMON : 1;
			unsigned short PBUSY : 1;
			unsigned short  : 3;
			unsigned short PID : 2;
#endif
	} BIT;
	} PIPE5CTR;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PID : 2;
			unsigned short  : 3;
			unsigned short PBUSY : 1;
			unsigned short SQMON : 1;
			unsigned short SQSET : 1;
			unsigned short SQCLR : 1;
			unsigned short ACLRM : 1;
			unsigned short  : 5;
			unsigned short BSTS : 1;
#else
			unsigned short BSTS : 1;
			unsigned short  : 5;
			unsigned short ACLRM : 1;
			unsigned short SQCLR : 1;
			unsigned short SQSET : 1;
			unsigned short SQMON : 1;
			unsigned short PBUSY : 1;
			unsigned short  : 3;
			unsigned short PID : 2;
#endif
	} BIT;
	} PIPE6CTR;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PID : 2;
			unsigned short  : 3;
			unsigned short PBUSY : 1;
			unsigned short SQMON : 1;
			unsigned short SQSET : 1;
			unsigned short SQCLR : 1;
			unsigned short ACLRM : 1;
			unsigned short  : 5;
			unsigned short BSTS : 1;
#else
			unsigned short BSTS : 1;
			unsigned short  : 5;
			unsigned short ACLRM : 1;
			unsigned short SQCLR : 1;
			unsigned short SQSET : 1;
			unsigned short SQMON : 1;
			unsigned short PBUSY : 1;
			unsigned short  : 3;
			unsigned short PID : 2;
#endif
	} BIT;
	} PIPE7CTR;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PID : 2;
			unsigned short  : 3;
			unsigned short PBUSY : 1;
			unsigned short SQMON : 1;
			unsigned short SQSET : 1;
			unsigned short SQCLR : 1;
			unsigned short ACLRM : 1;
			unsigned short  : 5;
			unsigned short BSTS : 1;
#else
			unsigned short BSTS : 1;
			unsigned short  : 5;
			unsigned short ACLRM : 1;
			unsigned short SQCLR : 1;
			unsigned short SQSET : 1;
			unsigned short SQMON : 1;
			unsigned short PBUSY : 1;
			unsigned short  : 3;
			unsigned short PID : 2;
#endif
	} BIT;
	} PIPE8CTR;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short PID : 2;
			unsigned short  : 3;
			unsigned short PBUSY : 1;
			unsigned short SQMON : 1;
			unsigned short SQSET : 1;
			unsigned short SQCLR : 1;
			unsigned short ACLRM : 1;
			unsigned short  : 5;
			unsigned short BSTS : 1;
#else
			unsigned short BSTS : 1;
			unsigned short  : 5;
			unsigned short ACLRM : 1;
			unsigned short SQCLR : 1;
			unsigned short SQSET : 1;
			unsigned short SQMON : 1;
			unsigned short PBUSY : 1;
			unsigned short  : 3;
			unsigned short PID : 2;
#endif
	} BIT;
	} PIPE9CTR;
	char           wk14[14];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 8;
			unsigned short TRCLR : 1;
			unsigned short TRENB : 1;
			unsigned short  : 6;
#else
			unsigned short  : 6;
			unsigned short TRENB : 1;
			unsigned short TRCLR : 1;
			unsigned short  : 8;
#endif
	} BIT;
	} PIPE1TRE;
	unsigned short PIPE1TRN;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 8;
			unsigned short TRCLR : 1;
			unsigned short TRENB : 1;
			unsigned short  : 6;
#else
			unsigned short  : 6;
			unsigned short TRENB : 1;
			unsigned short TRCLR : 1;
			unsigned short  : 8;
#endif
	} BIT;
	} PIPE2TRE;
	unsigned short PIPE2TRN;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 8;
			unsigned short TRCLR : 1;
			unsigned short TRENB : 1;
			unsigned short  : 6;
#else
			unsigned short  : 6;
			unsigned short TRENB : 1;
			unsigned short TRCLR : 1;
			unsigned short  : 8;
#endif
	} BIT;
	} PIPE3TRE;
	unsigned short PIPE3TRN;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 8;
			unsigned short TRCLR : 1;
			unsigned short TRENB : 1;
			unsigned short  : 6;
#else
			unsigned short  : 6;
			unsigned short TRENB : 1;
			unsigned short TRCLR : 1;
			unsigned short  : 8;
#endif
	} BIT;
	} PIPE4TRE;
	unsigned short PIPE4TRN;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 8;
			unsigned short TRCLR : 1;
			unsigned short TRENB : 1;
			unsigned short  : 6;
#else
			unsigned short  : 6;
			unsigned short TRENB : 1;
			unsigned short TRCLR : 1;
			unsigned short  : 8;
#endif
	} BIT;
	} PIPE5TRE;
	unsigned short PIPE5TRN;
	char           wk15[44];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 6;
			unsigned short USBSPD : 2;
			unsigned short  : 8;
#else
			unsigned short  : 8;
			unsigned short USBSPD : 2;
			unsigned short  : 6;
#endif
	} BIT;
	} DEVADD0;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 6;
			unsigned short USBSPD : 2;
			unsigned short  : 8;
#else
			unsigned short  : 8;
			unsigned short USBSPD : 2;
			unsigned short  : 6;
#endif
	} BIT;
	} DEVADD1;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 6;
			unsigned short USBSPD : 2;
			unsigned short  : 8;
#else
			unsigned short  : 8;
			unsigned short USBSPD : 2;
			unsigned short  : 6;
#endif
	} BIT;
	} DEVADD2;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 6;
			unsigned short USBSPD : 2;
			unsigned short  : 8;
#else
			unsigned short  : 8;
			unsigned short USBSPD : 2;
			unsigned short  : 6;
#endif
	} BIT;
	} DEVADD3;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 6;
			unsigned short USBSPD : 2;
			unsigned short  : 8;
#else
			unsigned short  : 8;
			unsigned short USBSPD : 2;
			unsigned short  : 6;
#endif
	} BIT;
	} DEVADD4;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short  : 6;
			unsigned short USBSPD : 2;
			unsigned short  : 8;
#else
			unsigned short  : 8;
			unsigned short USBSPD : 2;
			unsigned short  : 6;
#endif
	} BIT;
	} DEVADD5;
	char           wk16[20];
	union {
		unsigned long LONG;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned long SLEWR00 : 1;
			unsigned long SLEWR01 : 1;
			unsigned long SLEWF00 : 1;
			unsigned long SLEWF01 : 1;
			unsigned long  : 28;
#else
			unsigned long  : 28;
			unsigned long SLEWF01 : 1;
			unsigned long SLEWF00 : 1;
			unsigned long SLEWR01 : 1;
			unsigned long SLEWR00 : 1;
#endif
	} BIT;
	} PHYSLEW;
} st_usb0_t;

typedef struct st_wdt {
	unsigned char  WDTRR;
	char           wk0[1];
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short TOPS : 2;
			unsigned short  : 2;
			unsigned short CKS : 4;
			unsigned short RPES : 2;
			unsigned short  : 2;
			unsigned short RPSS : 2;
			unsigned short  : 2;
#else
			unsigned short  : 2;
			unsigned short RPSS : 2;
			unsigned short  : 2;
			unsigned short RPES : 2;
			unsigned short CKS : 4;
			unsigned short  : 2;
			unsigned short TOPS : 2;
#endif
	} BIT;
	} WDTCR;
	union {
		unsigned short WORD;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned short CNTVAL : 14;
			unsigned short UNDFF : 1;
			unsigned short REFEF : 1;
#else
			unsigned short REFEF : 1;
			unsigned short UNDFF : 1;
			unsigned short CNTVAL : 14;
#endif
	} BIT;
	} WDTSR;
	union {
		unsigned char BYTE;
		struct {
			
#ifdef __RX_LITTLE_ENDIAN__
			unsigned char  : 7;
			unsigned char RSTIRQS : 1;
#else
			unsigned char RSTIRQS : 1;
			unsigned char  : 7;
#endif
	} BIT;
	} WDTRCR;
} st_wdt_t;

typedef struct st_flashconst {
	unsigned long  UIDR0;
	unsigned long  UIDR1;
	unsigned long  UIDR2;
	unsigned long  UIDR3;
} st_flashconst_t;

typedef struct st_tempsconst {
	unsigned long  TSCDR;
} st_tempsconst_t;


#pragma pack()

#endif

