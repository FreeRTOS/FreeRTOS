/*******************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only
* intended for use with Renesas products. No other uses are authorized. This
* software is owned by Renesas Electronics Corporation and is protected under
* all applicable laws, including copyright laws.
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT
* LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE
* AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.
* TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS
* ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE
* FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR
* ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE
* BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software
* and to discontinue the availability of this software. By using this software,
* you agree to the additional terms and conditions found by accessing the
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2012 Renesas Electronics Corporation. All rights reserved.
*******************************************************************************/
/*******************************************************************************
* File Name    : intc_userdef.c
* $Rev: 17531 $
* $Date:: 2013-04-10 12:58:44 +0100#$
* Device(s)    : Aragon
* Tool-Chain   : DS-5 Ver 5.8
*              : ARM Complier
* OS           :
* H/W Platform : Aragon CPU Board
* Description  : Aragon Sample Program - Interrupt func table
* Operation    :
* Limitations  :
*******************************************************************************/


/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/
#include "r_typedefs.h"
#include "devdrv_intc.h"            /* INTC Driver Header */
#include "iodefine.h"

/* Do not include the following pragmas when compiling with IAR. */
#ifndef __ICCARM__
	#pragma arm section code   = "CODE_HANDLER_JMPTBL"
	#pragma arm section rodata = "CONST_HANDLER_JMPTBL"
	#pragma arm section rwdata = "DATA_HANDLER_JMPTBL"
	#pragma arm section zidata = "BSS_HANDLER_JMPTBL"
#else
	/* IAR requires intrinsics.h for the __enable_irq() function. */
	#include <intrinsics.h>
#endif

/******************************************************************************
Typedef definitions
******************************************************************************/


/******************************************************************************
Macro definitions
******************************************************************************/


/******************************************************************************
Imported global variables and functions (from other files)
******************************************************************************/


/******************************************************************************
Exported global variables and functions (to be accessed by other files)
******************************************************************************/


/******************************************************************************
Private global variables and functions
******************************************************************************/
/* ====  Prototype function ==== */
static void Userdef_INTC_Dummy_Interrupt(uint32_t int_sense);

/* ==== Global variable ==== */
static void (* intc_func_table[INTC_ID_TOTAL])(uint32_t int_sense) =
{
    Userdef_INTC_Dummy_Interrupt,        /* 0   : SW0           */
    Userdef_INTC_Dummy_Interrupt,        /* 1   : SW1           */
    Userdef_INTC_Dummy_Interrupt,        /* 2   : SW2           */
    Userdef_INTC_Dummy_Interrupt,        /* 3   : SW3           */
    Userdef_INTC_Dummy_Interrupt,        /* 4   : SW4           */
    Userdef_INTC_Dummy_Interrupt,        /* 5   : SW5           */
    Userdef_INTC_Dummy_Interrupt,        /* 6   : SW6           */
    Userdef_INTC_Dummy_Interrupt,        /* 7   : SW7           */
    Userdef_INTC_Dummy_Interrupt,        /* 8   : SW8           */
    Userdef_INTC_Dummy_Interrupt,        /* 9   : SW9           */
    Userdef_INTC_Dummy_Interrupt,        /* 10  : SW10          */
    Userdef_INTC_Dummy_Interrupt,        /* 11  : SW11          */
    Userdef_INTC_Dummy_Interrupt,        /* 12  : SW12          */
    Userdef_INTC_Dummy_Interrupt,        /* 13  : SW13          */
    Userdef_INTC_Dummy_Interrupt,        /* 14  : SW14          */
    Userdef_INTC_Dummy_Interrupt,        /* 15  : SW15          */
    Userdef_INTC_Dummy_Interrupt,        /* 16  : PMUIRQ0       */
    Userdef_INTC_Dummy_Interrupt,        /* 17  : COMMRX0       */
    Userdef_INTC_Dummy_Interrupt,        /* 18  : COMMTX0       */
    Userdef_INTC_Dummy_Interrupt,        /* 19  : CTIIRQ0       */
    Userdef_INTC_Dummy_Interrupt,        /* 20  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 21  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 22  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 23  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 24  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 25  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 26  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 27  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 28  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 29  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 30  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 31  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 32  : IRQ0          */
    Userdef_INTC_Dummy_Interrupt,        /* 33  : IRQ1          */
    Userdef_INTC_Dummy_Interrupt,        /* 34  : IRQ2          */
    Userdef_INTC_Dummy_Interrupt,        /* 35  : IRQ3          */
    Userdef_INTC_Dummy_Interrupt,        /* 36  : IRQ4          */
    Userdef_INTC_Dummy_Interrupt,        /* 37  : IRQ5          */
    Userdef_INTC_Dummy_Interrupt,        /* 38  : IRQ6          */
    Userdef_INTC_Dummy_Interrupt,        /* 39  : IRQ7          */
    Userdef_INTC_Dummy_Interrupt,        /* 40  : PL310ERR      */
    Userdef_INTC_Dummy_Interrupt,        /* 41  : DMAINT0       */
    Userdef_INTC_Dummy_Interrupt,        /* 42  : DMAINT1       */
    Userdef_INTC_Dummy_Interrupt,        /* 43  : DMAINT2       */
    Userdef_INTC_Dummy_Interrupt,        /* 44  : DMAINT3       */
    Userdef_INTC_Dummy_Interrupt,        /* 45  : DMAINT4       */
    Userdef_INTC_Dummy_Interrupt,        /* 46  : DMAINT5       */
    Userdef_INTC_Dummy_Interrupt,        /* 47  : DMAINT6       */
    Userdef_INTC_Dummy_Interrupt,        /* 48  : DMAINT7       */
    Userdef_INTC_Dummy_Interrupt,        /* 49  : DMAINT8       */
    Userdef_INTC_Dummy_Interrupt,        /* 50  : DMAINT9       */
    Userdef_INTC_Dummy_Interrupt,        /* 51  : DMAINT10      */
    Userdef_INTC_Dummy_Interrupt,        /* 52  : DMAINT11      */
    Userdef_INTC_Dummy_Interrupt,        /* 53  : DMAINT12      */
    Userdef_INTC_Dummy_Interrupt,        /* 54  : DMAINT13      */
    Userdef_INTC_Dummy_Interrupt,        /* 55  : DMAINT14      */
    Userdef_INTC_Dummy_Interrupt,        /* 56  : DMAINT15      */
    Userdef_INTC_Dummy_Interrupt,        /* 57  : DMAERR        */
    Userdef_INTC_Dummy_Interrupt,        /* 58  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 59  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 60  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 61  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 62  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 63  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 64  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 65  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 66  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 67  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 68  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 69  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 70  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 71  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 72  : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 73  : USBI0         */
    Userdef_INTC_Dummy_Interrupt,        /* 74  : USBI1         */
    Userdef_INTC_Dummy_Interrupt,        /* 75  : S0_VI_VSYNC0  */
    Userdef_INTC_Dummy_Interrupt,        /* 76  : S0_LO_VSYNC0  */
    Userdef_INTC_Dummy_Interrupt,        /* 77  : S0_VSYNCERR0  */
    Userdef_INTC_Dummy_Interrupt,        /* 78  : GR3_VLINE0    */
    Userdef_INTC_Dummy_Interrupt,        /* 79  : S0_VFIELD0    */
    Userdef_INTC_Dummy_Interrupt,        /* 80  : IV1_VBUFERR0  */
    Userdef_INTC_Dummy_Interrupt,        /* 81  : IV3_VBUFERR0  */
    Userdef_INTC_Dummy_Interrupt,        /* 82  : IV5_VBUFERR0  */
    Userdef_INTC_Dummy_Interrupt,        /* 83  : IV6_VBUFERR0  */
    Userdef_INTC_Dummy_Interrupt,        /* 84  : S0_WLINE0     */
    Userdef_INTC_Dummy_Interrupt,        /* 85  : S1_VI_VSYNC0  */
    Userdef_INTC_Dummy_Interrupt,        /* 86  : S1_LO_VSYNC0  */
    Userdef_INTC_Dummy_Interrupt,        /* 87  : S1_VSYNCERR0  */
    Userdef_INTC_Dummy_Interrupt,        /* 88  : S1_VFIELD0    */
    Userdef_INTC_Dummy_Interrupt,        /* 89  : IV2_VBUFERR0  */
    Userdef_INTC_Dummy_Interrupt,        /* 90  : IV4_VBUFERR0  */
    Userdef_INTC_Dummy_Interrupt,        /* 91  : S1_WLINE0     */
    Userdef_INTC_Dummy_Interrupt,        /* 92  : OIR_VI_VSYNC0 */
    Userdef_INTC_Dummy_Interrupt,        /* 93  : OIR_LO_VSYNC0 */
    Userdef_INTC_Dummy_Interrupt,        /* 94  : OIR_VSYNCERR0 */
    Userdef_INTC_Dummy_Interrupt,        /* 95  : OIR_VFIELD0   */
    Userdef_INTC_Dummy_Interrupt,        /* 96  : IV7_VBUFERR0  */
    Userdef_INTC_Dummy_Interrupt,        /* 97  : IV8_VBUFERR0  */
    Userdef_INTC_Dummy_Interrupt,        /* 98  : OIR_WLINE0    */
    Userdef_INTC_Dummy_Interrupt,        /* 99  : S0_VI_VSYNC1  */
    Userdef_INTC_Dummy_Interrupt,        /* 100 : S0_LO_VSYNC1  */
    Userdef_INTC_Dummy_Interrupt,        /* 101 : S0_VSYNCERR1  */
    Userdef_INTC_Dummy_Interrupt,        /* 102 : GR3_VLINE1    */
    Userdef_INTC_Dummy_Interrupt,        /* 103 : S0_VFIELD1    */
    Userdef_INTC_Dummy_Interrupt,        /* 104 : IV1_VBUFERR1  */
    Userdef_INTC_Dummy_Interrupt,        /* 105 : IV3_VBUFERR1  */
    Userdef_INTC_Dummy_Interrupt,        /* 106 : IV5_VBUFERR1  */
    Userdef_INTC_Dummy_Interrupt,        /* 107 : IV6_VBUFERR1  */
    Userdef_INTC_Dummy_Interrupt,        /* 108 : S0_WLINE1     */
    Userdef_INTC_Dummy_Interrupt,        /* 109 : S1_VI_VSYNC1  */
    Userdef_INTC_Dummy_Interrupt,        /* 110 : S1_LO_VSYNC1  */
    Userdef_INTC_Dummy_Interrupt,        /* 111 : S1_VSYNCERR1  */
    Userdef_INTC_Dummy_Interrupt,        /* 112 : S1_VFIELD1    */
    Userdef_INTC_Dummy_Interrupt,        /* 113 : IV2_VBUFERR1  */
    Userdef_INTC_Dummy_Interrupt,        /* 114 : IV4_VBUFERR1  */
    Userdef_INTC_Dummy_Interrupt,        /* 115 : S1_WLINE1     */
    Userdef_INTC_Dummy_Interrupt,        /* 116 : OIR_VI_VSYNC1 */
    Userdef_INTC_Dummy_Interrupt,        /* 117 : OIR_LO_VSYNC1 */
    Userdef_INTC_Dummy_Interrupt,        /* 118 : OIR_VLINE1    */
    Userdef_INTC_Dummy_Interrupt,        /* 119 : OIR_VFIELD1   */
    Userdef_INTC_Dummy_Interrupt,        /* 120 : IV7_VBUFERR1  */
    Userdef_INTC_Dummy_Interrupt,        /* 121 : IV8_VBUFERR1  */
    Userdef_INTC_Dummy_Interrupt,        /* 122 : OIR_WLINE1    */
    Userdef_INTC_Dummy_Interrupt,        /* 123 : IMRDI         */
    Userdef_INTC_Dummy_Interrupt,        /* 124 : IMR2I0        */
    Userdef_INTC_Dummy_Interrupt,        /* 125 : IMR2I1        */
    Userdef_INTC_Dummy_Interrupt,        /* 126 : JEDI          */
    Userdef_INTC_Dummy_Interrupt,        /* 127 : JDTI          */
    Userdef_INTC_Dummy_Interrupt,        /* 128 : CMP0          */
    Userdef_INTC_Dummy_Interrupt,        /* 129 : CMP1          */
    Userdef_INTC_Dummy_Interrupt,        /* 130 : INT0          */
    Userdef_INTC_Dummy_Interrupt,        /* 131 : INT1          */
    Userdef_INTC_Dummy_Interrupt,        /* 132 : INT2          */
    Userdef_INTC_Dummy_Interrupt,        /* 133 : INT3          */
    Userdef_INTC_Dummy_Interrupt,        /* 134 : OSTMI0        */
    Userdef_INTC_Dummy_Interrupt,        /* 135 : OSTMI1        */
    Userdef_INTC_Dummy_Interrupt,        /* 136 : CMI           */
    Userdef_INTC_Dummy_Interrupt,        /* 137 : WTOUT         */
    Userdef_INTC_Dummy_Interrupt,        /* 138 : ITI           */
    Userdef_INTC_Dummy_Interrupt,        /* 139 : TGI0A         */
    Userdef_INTC_Dummy_Interrupt,        /* 140 : TGI0B         */
    Userdef_INTC_Dummy_Interrupt,        /* 141 : TGI0C         */
    Userdef_INTC_Dummy_Interrupt,        /* 142 : TGI0D         */
    Userdef_INTC_Dummy_Interrupt,        /* 143 : TGI0V         */
    Userdef_INTC_Dummy_Interrupt,        /* 144 : TGI0E         */
    Userdef_INTC_Dummy_Interrupt,        /* 145 : TGI0F         */
    Userdef_INTC_Dummy_Interrupt,        /* 146 : TGI1A         */
    Userdef_INTC_Dummy_Interrupt,        /* 147 : TGI1B         */
    Userdef_INTC_Dummy_Interrupt,        /* 148 : TGI1V         */
    Userdef_INTC_Dummy_Interrupt,        /* 149 : TGI1U         */
    Userdef_INTC_Dummy_Interrupt,        /* 150 : TGI2A         */
    Userdef_INTC_Dummy_Interrupt,        /* 151 : TGI2B         */
    Userdef_INTC_Dummy_Interrupt,        /* 152 : TGI2V         */
    Userdef_INTC_Dummy_Interrupt,        /* 153 : TGI2U         */
    Userdef_INTC_Dummy_Interrupt,        /* 154 : TGI3A         */
    Userdef_INTC_Dummy_Interrupt,        /* 155 : TGI3B         */
    Userdef_INTC_Dummy_Interrupt,        /* 156 : TGI3C         */
    Userdef_INTC_Dummy_Interrupt,        /* 157 : TGI3D         */
    Userdef_INTC_Dummy_Interrupt,        /* 158 : TGI3V         */
    Userdef_INTC_Dummy_Interrupt,        /* 159 : TGI4A         */
    Userdef_INTC_Dummy_Interrupt,        /* 160 : TGI4B         */
    Userdef_INTC_Dummy_Interrupt,        /* 161 : TGI4C         */
    Userdef_INTC_Dummy_Interrupt,        /* 162 : TGI4D         */
    Userdef_INTC_Dummy_Interrupt,        /* 163 : TGI4V         */
    Userdef_INTC_Dummy_Interrupt,        /* 164 : CMI1          */
    Userdef_INTC_Dummy_Interrupt,        /* 165 : CMI2          */
    Userdef_INTC_Dummy_Interrupt,        /* 166 : SGDEI0        */
    Userdef_INTC_Dummy_Interrupt,        /* 167 : SGDEI1        */
    Userdef_INTC_Dummy_Interrupt,        /* 168 : SGDEI2        */
    Userdef_INTC_Dummy_Interrupt,        /* 169 : SGDEI3        */
    Userdef_INTC_Dummy_Interrupt,        /* 170 : ADI           */
    Userdef_INTC_Dummy_Interrupt,        /* 171 : ADWAR         */
    Userdef_INTC_Dummy_Interrupt,        /* 172 : SSII0         */
    Userdef_INTC_Dummy_Interrupt,        /* 173 : SSIRXI0       */
    Userdef_INTC_Dummy_Interrupt,        /* 174 : SSITXI0       */
    Userdef_INTC_Dummy_Interrupt,        /* 175 : SSII1         */
    Userdef_INTC_Dummy_Interrupt,        /* 176 : SSIRXI1       */
    Userdef_INTC_Dummy_Interrupt,        /* 177 : SSITXI1       */
    Userdef_INTC_Dummy_Interrupt,        /* 178 : SSII2         */
    Userdef_INTC_Dummy_Interrupt,        /* 179 : SSIRTI2       */
    Userdef_INTC_Dummy_Interrupt,        /* 180 : SSII3         */
    Userdef_INTC_Dummy_Interrupt,        /* 181 : SSIRXI3       */
    Userdef_INTC_Dummy_Interrupt,        /* 182 : SSITXI3       */
    Userdef_INTC_Dummy_Interrupt,        /* 183 : SSII4         */
    Userdef_INTC_Dummy_Interrupt,        /* 184 : SSIRTI4       */
    Userdef_INTC_Dummy_Interrupt,        /* 185 : SSII5         */
    Userdef_INTC_Dummy_Interrupt,        /* 186 : SSIRXI5       */
    Userdef_INTC_Dummy_Interrupt,        /* 187 : SSITXI5       */
    Userdef_INTC_Dummy_Interrupt,        /* 188 : SPDIFI        */
    Userdef_INTC_Dummy_Interrupt,        /* 189 : TEI0          */
    Userdef_INTC_Dummy_Interrupt,        /* 190 : RI0           */
    Userdef_INTC_Dummy_Interrupt,        /* 191 : TI0           */
    Userdef_INTC_Dummy_Interrupt,        /* 192 : SPI0          */
    Userdef_INTC_Dummy_Interrupt,        /* 193 : STI0          */
    Userdef_INTC_Dummy_Interrupt,        /* 194 : NAKI0         */
    Userdef_INTC_Dummy_Interrupt,        /* 195 : ALI0          */
    Userdef_INTC_Dummy_Interrupt,        /* 196 : TMOI0         */
    Userdef_INTC_Dummy_Interrupt,        /* 197 : TEI1          */
    Userdef_INTC_Dummy_Interrupt,        /* 198 : RI1           */
    Userdef_INTC_Dummy_Interrupt,        /* 199 : TI1           */
    Userdef_INTC_Dummy_Interrupt,        /* 200 : SPI1          */
    Userdef_INTC_Dummy_Interrupt,        /* 201 : STI1          */
    Userdef_INTC_Dummy_Interrupt,        /* 202 : NAKI1         */
    Userdef_INTC_Dummy_Interrupt,        /* 203 : ALI1          */
    Userdef_INTC_Dummy_Interrupt,        /* 204 : TMOI1         */
    Userdef_INTC_Dummy_Interrupt,        /* 205 : TEI2          */
    Userdef_INTC_Dummy_Interrupt,        /* 206 : RI2           */
    Userdef_INTC_Dummy_Interrupt,        /* 207 : TI2           */
    Userdef_INTC_Dummy_Interrupt,        /* 208 : SPI2          */
    Userdef_INTC_Dummy_Interrupt,        /* 209 : STI2          */
    Userdef_INTC_Dummy_Interrupt,        /* 210 : NAKI2         */
    Userdef_INTC_Dummy_Interrupt,        /* 211 : ALI2          */
    Userdef_INTC_Dummy_Interrupt,        /* 212 : TMOI2         */
    Userdef_INTC_Dummy_Interrupt,        /* 213 : TEI3          */
    Userdef_INTC_Dummy_Interrupt,        /* 214 : RI3           */
    Userdef_INTC_Dummy_Interrupt,        /* 215 : TI3           */
    Userdef_INTC_Dummy_Interrupt,        /* 216 : SPI3          */
    Userdef_INTC_Dummy_Interrupt,        /* 217 : STI3          */
    Userdef_INTC_Dummy_Interrupt,        /* 218 : NAKI3         */
    Userdef_INTC_Dummy_Interrupt,        /* 219 : ALI3          */
    Userdef_INTC_Dummy_Interrupt,        /* 220 : TMOI3         */
    Userdef_INTC_Dummy_Interrupt,        /* 221 : BRI0          */
    Userdef_INTC_Dummy_Interrupt,        /* 222 : ERI0          */
    Userdef_INTC_Dummy_Interrupt,        /* 223 : RXI0          */
    Userdef_INTC_Dummy_Interrupt,        /* 224 : TXI0          */
    Userdef_INTC_Dummy_Interrupt,        /* 225 : BRI1          */
    Userdef_INTC_Dummy_Interrupt,        /* 226 : ERI1          */
    Userdef_INTC_Dummy_Interrupt,        /* 227 : RXI1          */
    Userdef_INTC_Dummy_Interrupt,        /* 228 : TXI1          */
    Userdef_INTC_Dummy_Interrupt,        /* 229 : BRI2          */
    Userdef_INTC_Dummy_Interrupt,        /* 230 : ERI2          */
    Userdef_INTC_Dummy_Interrupt,        /* 231 : RXI2          */
    Userdef_INTC_Dummy_Interrupt,        /* 232 : TXI2          */
    Userdef_INTC_Dummy_Interrupt,        /* 233 : BRI3          */
    Userdef_INTC_Dummy_Interrupt,        /* 234 : ERI3          */
    Userdef_INTC_Dummy_Interrupt,        /* 235 : RXI3          */
    Userdef_INTC_Dummy_Interrupt,        /* 236 : TXI3          */
    Userdef_INTC_Dummy_Interrupt,        /* 237 : BRI4          */
    Userdef_INTC_Dummy_Interrupt,        /* 238 : ERI4          */
    Userdef_INTC_Dummy_Interrupt,        /* 239 : RXI4          */
    Userdef_INTC_Dummy_Interrupt,        /* 240 : TXI4          */
    Userdef_INTC_Dummy_Interrupt,        /* 241 : BRI5          */
    Userdef_INTC_Dummy_Interrupt,        /* 242 : ERI5          */
    Userdef_INTC_Dummy_Interrupt,        /* 243 : RXI5          */
    Userdef_INTC_Dummy_Interrupt,        /* 244 : TXI5          */
    Userdef_INTC_Dummy_Interrupt,        /* 245 : BRI6          */
    Userdef_INTC_Dummy_Interrupt,        /* 246 : ERI6          */
    Userdef_INTC_Dummy_Interrupt,        /* 247 : RXI6          */
    Userdef_INTC_Dummy_Interrupt,        /* 248 : TXI6          */
    Userdef_INTC_Dummy_Interrupt,        /* 249 : BRI7          */
    Userdef_INTC_Dummy_Interrupt,        /* 250 : ERI7          */
    Userdef_INTC_Dummy_Interrupt,        /* 251 : RXI7          */
    Userdef_INTC_Dummy_Interrupt,        /* 252 : TXI7          */
    Userdef_INTC_Dummy_Interrupt,        /* 253 : GERI          */
    Userdef_INTC_Dummy_Interrupt,        /* 254 : RFI           */
    Userdef_INTC_Dummy_Interrupt,        /* 255 : CFRXI0        */
    Userdef_INTC_Dummy_Interrupt,        /* 256 : CERI0         */
    Userdef_INTC_Dummy_Interrupt,        /* 257 : CTXI0         */
    Userdef_INTC_Dummy_Interrupt,        /* 258 : CFRXI1        */
    Userdef_INTC_Dummy_Interrupt,        /* 259 : CERI1         */
    Userdef_INTC_Dummy_Interrupt,        /* 260 : CTXI1         */
    Userdef_INTC_Dummy_Interrupt,        /* 261 : CFRXI2        */
    Userdef_INTC_Dummy_Interrupt,        /* 262 : CERI2         */
    Userdef_INTC_Dummy_Interrupt,        /* 263 : CTXI2         */
    Userdef_INTC_Dummy_Interrupt,        /* 264 : CFRXI3        */
    Userdef_INTC_Dummy_Interrupt,        /* 265 : CERI3         */
    Userdef_INTC_Dummy_Interrupt,        /* 266 : CTXI3         */
    Userdef_INTC_Dummy_Interrupt,        /* 267 : CFRXI4        */
    Userdef_INTC_Dummy_Interrupt,        /* 268 : CERI4         */
    Userdef_INTC_Dummy_Interrupt,        /* 269 : CTXI4         */
    Userdef_INTC_Dummy_Interrupt,        /* 270 : SPEI0         */
    Userdef_INTC_Dummy_Interrupt,        /* 271 : SPRI0         */
    Userdef_INTC_Dummy_Interrupt,        /* 272 : SPTI0         */
    Userdef_INTC_Dummy_Interrupt,        /* 273 : SPEI1         */
    Userdef_INTC_Dummy_Interrupt,        /* 274 : SPRI1         */
    Userdef_INTC_Dummy_Interrupt,        /* 275 : SPTI1         */
    Userdef_INTC_Dummy_Interrupt,        /* 276 : SPEI2         */
    Userdef_INTC_Dummy_Interrupt,        /* 277 : SPRI2         */
    Userdef_INTC_Dummy_Interrupt,        /* 278 : SPTI2         */
    Userdef_INTC_Dummy_Interrupt,        /* 279 : SPEI3         */
    Userdef_INTC_Dummy_Interrupt,        /* 280 : SPRI3         */
    Userdef_INTC_Dummy_Interrupt,        /* 281 : SPTI3         */
    Userdef_INTC_Dummy_Interrupt,        /* 282 : SPEI4         */
    Userdef_INTC_Dummy_Interrupt,        /* 283 : SPRI4         */
    Userdef_INTC_Dummy_Interrupt,        /* 284 : SPTI4         */
    Userdef_INTC_Dummy_Interrupt,        /* 285 : IEBBTD        */
    Userdef_INTC_Dummy_Interrupt,        /* 286 : IEBBTERR      */
    Userdef_INTC_Dummy_Interrupt,        /* 287 : IEBBTSTA      */
    Userdef_INTC_Dummy_Interrupt,        /* 288 : IEBBTV        */
    Userdef_INTC_Dummy_Interrupt,        /* 289 : ISY           */
    Userdef_INTC_Dummy_Interrupt,        /* 290 : IERR          */
    Userdef_INTC_Dummy_Interrupt,        /* 291 : ITARG         */
    Userdef_INTC_Dummy_Interrupt,        /* 292 : ISEC          */
    Userdef_INTC_Dummy_Interrupt,        /* 293 : IBUF          */
    Userdef_INTC_Dummy_Interrupt,        /* 294 : IREADY        */
    Userdef_INTC_Dummy_Interrupt,        /* 295 : FLSTE         */
    Userdef_INTC_Dummy_Interrupt,        /* 296 : FLTENDI       */
    Userdef_INTC_Dummy_Interrupt,        /* 297 : FLTREQ0I      */
    Userdef_INTC_Dummy_Interrupt,        /* 298 : FLTREQ1I      */
    Userdef_INTC_Dummy_Interrupt,        /* 299 : MMC0          */
    Userdef_INTC_Dummy_Interrupt,        /* 300 : MMC1          */
    Userdef_INTC_Dummy_Interrupt,        /* 301 : MMC2          */
    Userdef_INTC_Dummy_Interrupt,        /* 302 : SDHI0_3       */
    Userdef_INTC_Dummy_Interrupt,        /* 303 : SDHI0_0       */
    Userdef_INTC_Dummy_Interrupt,        /* 304 : SDHI0_1       */
    Userdef_INTC_Dummy_Interrupt,        /* 305 : SDHI1_3       */
    Userdef_INTC_Dummy_Interrupt,        /* 306 : SDHI1_0       */
    Userdef_INTC_Dummy_Interrupt,        /* 307 : SDHI1_1       */
    Userdef_INTC_Dummy_Interrupt,        /* 308 : ARM           */
    Userdef_INTC_Dummy_Interrupt,        /* 309 : PRD           */
    Userdef_INTC_Dummy_Interrupt,        /* 310 : CUP           */
    Userdef_INTC_Dummy_Interrupt,        /* 311 : SCUAI0        */
    Userdef_INTC_Dummy_Interrupt,        /* 312 : SCUAI1        */
    Userdef_INTC_Dummy_Interrupt,        /* 313 : SCUFDI0       */
    Userdef_INTC_Dummy_Interrupt,        /* 314 : SCUFDI1       */
    Userdef_INTC_Dummy_Interrupt,        /* 315 : SCUFDI2       */
    Userdef_INTC_Dummy_Interrupt,        /* 316 : SCUFDI3       */
    Userdef_INTC_Dummy_Interrupt,        /* 317 : SCUFUI0       */
    Userdef_INTC_Dummy_Interrupt,        /* 318 : SCUFUI1       */
    Userdef_INTC_Dummy_Interrupt,        /* 319 : SCUFUI2       */
    Userdef_INTC_Dummy_Interrupt,        /* 320 : SCUFUI3       */
    Userdef_INTC_Dummy_Interrupt,        /* 321 : SCUDVI0       */
    Userdef_INTC_Dummy_Interrupt,        /* 322 : SCUDVI1       */
    Userdef_INTC_Dummy_Interrupt,        /* 323 : SCUDVI2       */
    Userdef_INTC_Dummy_Interrupt,        /* 324 : SCUDVI3       */
    Userdef_INTC_Dummy_Interrupt,        /* 325 : MLBCI         */
    Userdef_INTC_Dummy_Interrupt,        /* 326 : MLBSI         */
    Userdef_INTC_Dummy_Interrupt,        /* 327 : DRC0          */
    Userdef_INTC_Dummy_Interrupt,        /* 328 : DRC1          */
    Userdef_INTC_Dummy_Interrupt,        /* 329 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 330 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 331 : LINI0_INT_T   */
    Userdef_INTC_Dummy_Interrupt,        /* 332 : LINI0_INT_R   */
    Userdef_INTC_Dummy_Interrupt,        /* 333 : LINI0_INT_S   */
    Userdef_INTC_Dummy_Interrupt,        /* 334 : LINI0_INT_M   */
    Userdef_INTC_Dummy_Interrupt,        /* 335 : LINI1_INT_T   */
    Userdef_INTC_Dummy_Interrupt,        /* 336 : LINI1_INT_R   */
    Userdef_INTC_Dummy_Interrupt,        /* 337 : LINI1_INT_S   */
    Userdef_INTC_Dummy_Interrupt,        /* 338 : LINI1_INT_M   */
    Userdef_INTC_Dummy_Interrupt,        /* 339 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 340 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 341 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 342 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 343 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 344 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 345 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 346 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 347 : ERI0          */
    Userdef_INTC_Dummy_Interrupt,        /* 348 : RXI0          */
    Userdef_INTC_Dummy_Interrupt,        /* 349 : TXI0          */
    Userdef_INTC_Dummy_Interrupt,        /* 350 : TEI0          */
    Userdef_INTC_Dummy_Interrupt,        /* 351 : ERI1          */
    Userdef_INTC_Dummy_Interrupt,        /* 352 : RXI1          */
    Userdef_INTC_Dummy_Interrupt,        /* 353 : TXI1          */
    Userdef_INTC_Dummy_Interrupt,        /* 354 : TEI1          */
    Userdef_INTC_Dummy_Interrupt,        /* 355 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 356 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 357 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 358 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 359 : ETHERI        */
    Userdef_INTC_Dummy_Interrupt,        /* 360 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 361 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 362 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 363 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 364 : CEUI          */
    Userdef_INTC_Dummy_Interrupt,        /* 365 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 366 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 367 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 368 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 369 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 370 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 371 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 372 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 373 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 374 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 375 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 376 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 377 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 378 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 379 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 380 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 381 : H2XMLB_ERRINT */
    Userdef_INTC_Dummy_Interrupt,        /* 382 : H2XIC1_ERRINT */
    Userdef_INTC_Dummy_Interrupt,        /* 383 : X2HPERI1_ERRINT*/
    Userdef_INTC_Dummy_Interrupt,        /* 384 : X2HPERI2_ERRINT*/
    Userdef_INTC_Dummy_Interrupt,        /* 385 : X2HPERI34_ERRINT*/
    Userdef_INTC_Dummy_Interrupt,        /* 386 : X2HPERI5_ERRINT*/
    Userdef_INTC_Dummy_Interrupt,        /* 387 : X2HPERI67_ERRINT*/
    Userdef_INTC_Dummy_Interrupt,        /* 388 : X2HDBGR_ERRINT*/
    Userdef_INTC_Dummy_Interrupt,        /* 389 : X2HBSC_ERRINT */
    Userdef_INTC_Dummy_Interrupt,        /* 390 : X2HSPI1_ERRINT*/
    Userdef_INTC_Dummy_Interrupt,        /* 391 : X2HSPI2_ERRINT*/
    Userdef_INTC_Dummy_Interrupt,        /* 392 : PRRI          */
    Userdef_INTC_Dummy_Interrupt,        /* 393 : IFEI0         */
    Userdef_INTC_Dummy_Interrupt,        /* 394 : OFFI0         */
    Userdef_INTC_Dummy_Interrupt,        /* 395 : PFVEI0        */
    Userdef_INTC_Dummy_Interrupt,        /* 396 : IFEI1         */
    Userdef_INTC_Dummy_Interrupt,        /* 397 : OFFI1         */
    Userdef_INTC_Dummy_Interrupt,        /* 398 : PFVEI1        */
    Userdef_INTC_Dummy_Interrupt,        /* 399 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 400 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 401 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 402 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 403 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 404 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 405 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 406 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 407 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 408 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 409 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 410 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 411 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 412 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 413 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 414 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 415 : <reserved>    */
    Userdef_INTC_Dummy_Interrupt,        /* 416 : TINT0         */
    Userdef_INTC_Dummy_Interrupt,        /* 417 : TINT1         */
    Userdef_INTC_Dummy_Interrupt,        /* 418 : TINT2         */
    Userdef_INTC_Dummy_Interrupt,        /* 419 : TINT3         */
    Userdef_INTC_Dummy_Interrupt,        /* 420 : TINT4         */
    Userdef_INTC_Dummy_Interrupt,        /* 421 : TINT5         */
    Userdef_INTC_Dummy_Interrupt,        /* 422 : TINT6         */
    Userdef_INTC_Dummy_Interrupt,        /* 423 : TINT7         */
    Userdef_INTC_Dummy_Interrupt,        /* 424 : TINT8         */
    Userdef_INTC_Dummy_Interrupt,        /* 425 : TINT9         */
    Userdef_INTC_Dummy_Interrupt,        /* 426 : TINT10        */
    Userdef_INTC_Dummy_Interrupt,        /* 427 : TINT11        */
    Userdef_INTC_Dummy_Interrupt,        /* 428 : TINT12        */
    Userdef_INTC_Dummy_Interrupt,        /* 429 : TINT13        */
    Userdef_INTC_Dummy_Interrupt,        /* 430 : TINT14        */
    Userdef_INTC_Dummy_Interrupt,        /* 431 : TINT15        */
    Userdef_INTC_Dummy_Interrupt,        /* 432 : TINT16        */
    Userdef_INTC_Dummy_Interrupt,        /* 433 : TINT17        */
    Userdef_INTC_Dummy_Interrupt,        /* 434 : TINT18        */
    Userdef_INTC_Dummy_Interrupt,        /* 435 : TINT19        */
    Userdef_INTC_Dummy_Interrupt,        /* 436 : TINT20        */
    Userdef_INTC_Dummy_Interrupt,        /* 437 : TINT21        */
    Userdef_INTC_Dummy_Interrupt,        /* 438 : TINT22        */
    Userdef_INTC_Dummy_Interrupt,        /* 439 : TINT23        */
    Userdef_INTC_Dummy_Interrupt,        /* 440 : TINT24        */
    Userdef_INTC_Dummy_Interrupt,        /* 441 : TINT25        */
    Userdef_INTC_Dummy_Interrupt,        /* 442 : TINT26        */
    Userdef_INTC_Dummy_Interrupt,        /* 443 : TINT27        */
    Userdef_INTC_Dummy_Interrupt,        /* 444 : TINT28        */
    Userdef_INTC_Dummy_Interrupt,        /* 445 : TINT29        */
    Userdef_INTC_Dummy_Interrupt,        /* 446 : TINT30        */
    Userdef_INTC_Dummy_Interrupt,        /* 447 : TINT31        */
    Userdef_INTC_Dummy_Interrupt,        /* 448 : TINT32        */
    Userdef_INTC_Dummy_Interrupt,        /* 449 : TINT33        */
    Userdef_INTC_Dummy_Interrupt,        /* 450 : TINT34        */
    Userdef_INTC_Dummy_Interrupt,        /* 451 : TINT35        */
    Userdef_INTC_Dummy_Interrupt,        /* 452 : TINT36        */
    Userdef_INTC_Dummy_Interrupt,        /* 453 : TINT37        */
    Userdef_INTC_Dummy_Interrupt,        /* 454 : TINT38        */
    Userdef_INTC_Dummy_Interrupt,        /* 455 : TINT39        */
    Userdef_INTC_Dummy_Interrupt,        /* 456 : TINT40        */
    Userdef_INTC_Dummy_Interrupt,        /* 457 : TINT41        */
    Userdef_INTC_Dummy_Interrupt,        /* 458 : TINT42        */
    Userdef_INTC_Dummy_Interrupt,        /* 459 : TINT43        */
    Userdef_INTC_Dummy_Interrupt,        /* 460 : TINT44        */
    Userdef_INTC_Dummy_Interrupt,        /* 461 : TINT45        */
    Userdef_INTC_Dummy_Interrupt,        /* 462 : TINT46        */
    Userdef_INTC_Dummy_Interrupt,        /* 463 : TINT47        */
    Userdef_INTC_Dummy_Interrupt,        /* 464 : TINT48        */
    Userdef_INTC_Dummy_Interrupt,        /* 465 : TINT49        */
    Userdef_INTC_Dummy_Interrupt,        /* 466 : TINT50        */
    Userdef_INTC_Dummy_Interrupt,        /* 467 : TINT51        */
    Userdef_INTC_Dummy_Interrupt,        /* 468 : TINT52        */
    Userdef_INTC_Dummy_Interrupt,        /* 469 : TINT53        */
    Userdef_INTC_Dummy_Interrupt,        /* 470 : TINT54        */
    Userdef_INTC_Dummy_Interrupt,        /* 471 : TINT55        */
    Userdef_INTC_Dummy_Interrupt,        /* 472 : TINT56        */
    Userdef_INTC_Dummy_Interrupt,        /* 473 : TINT57        */
    Userdef_INTC_Dummy_Interrupt,        /* 474 : TINT58        */
    Userdef_INTC_Dummy_Interrupt,        /* 475 : TINT59        */
    Userdef_INTC_Dummy_Interrupt,        /* 476 : TINT60        */
    Userdef_INTC_Dummy_Interrupt,        /* 477 : TINT61        */
    Userdef_INTC_Dummy_Interrupt,        /* 478 : TINT62        */
    Userdef_INTC_Dummy_Interrupt,        /* 479 : TINT63        */
    Userdef_INTC_Dummy_Interrupt,        /* 480 : TINT64        */
    Userdef_INTC_Dummy_Interrupt,        /* 481 : TINT65        */
    Userdef_INTC_Dummy_Interrupt,        /* 482 : TINT66        */
    Userdef_INTC_Dummy_Interrupt,        /* 483 : TINT67        */
    Userdef_INTC_Dummy_Interrupt,        /* 484 : TINT68        */
    Userdef_INTC_Dummy_Interrupt,        /* 485 : TINT69        */
    Userdef_INTC_Dummy_Interrupt,        /* 486 : TINT70        */
    Userdef_INTC_Dummy_Interrupt,        /* 487 : TINT71        */
    Userdef_INTC_Dummy_Interrupt,        /* 488 : TINT72        */
    Userdef_INTC_Dummy_Interrupt,        /* 489 : TINT73        */
    Userdef_INTC_Dummy_Interrupt,        /* 490 : TINT74        */
    Userdef_INTC_Dummy_Interrupt,        /* 491 : TINT75        */
    Userdef_INTC_Dummy_Interrupt,        /* 492 : TINT76        */
    Userdef_INTC_Dummy_Interrupt,        /* 493 : TINT77        */
    Userdef_INTC_Dummy_Interrupt,        /* 494 : TINT78        */
    Userdef_INTC_Dummy_Interrupt,        /* 495 : TINT79        */
    Userdef_INTC_Dummy_Interrupt,        /* 496 : TINT80        */
    Userdef_INTC_Dummy_Interrupt,        /* 497 : TINT81        */
    Userdef_INTC_Dummy_Interrupt,        /* 498 : TINT82        */
    Userdef_INTC_Dummy_Interrupt,        /* 499 : TINT83        */
    Userdef_INTC_Dummy_Interrupt,        /* 500 : TINT84        */
    Userdef_INTC_Dummy_Interrupt,        /* 501 : TINT85        */
    Userdef_INTC_Dummy_Interrupt,        /* 502 : TINT86        */
    Userdef_INTC_Dummy_Interrupt,        /* 503 : TINT87        */
    Userdef_INTC_Dummy_Interrupt,        /* 504 : TINT88        */
    Userdef_INTC_Dummy_Interrupt,        /* 505 : TINT89        */
    Userdef_INTC_Dummy_Interrupt,        /* 506 : TINT90        */
    Userdef_INTC_Dummy_Interrupt,        /* 507 : TINT91        */
    Userdef_INTC_Dummy_Interrupt,        /* 508 : TINT92        */
    Userdef_INTC_Dummy_Interrupt,        /* 509 : TINT93        */
    Userdef_INTC_Dummy_Interrupt,        /* 510 : TINT94        */
    Userdef_INTC_Dummy_Interrupt,        /* 511 : TINT95        */
    Userdef_INTC_Dummy_Interrupt,        /* 512 : TINT96        */
    Userdef_INTC_Dummy_Interrupt,        /* 513 : TINT97        */
    Userdef_INTC_Dummy_Interrupt,        /* 514 : TINT98        */
    Userdef_INTC_Dummy_Interrupt,        /* 515 : TINT99        */
    Userdef_INTC_Dummy_Interrupt,        /* 516 : TINT100       */
    Userdef_INTC_Dummy_Interrupt,        /* 517 : TINT101       */
    Userdef_INTC_Dummy_Interrupt,        /* 518 : TINT102       */
    Userdef_INTC_Dummy_Interrupt,        /* 519 : TINT103       */
    Userdef_INTC_Dummy_Interrupt,        /* 520 : TINT104       */
    Userdef_INTC_Dummy_Interrupt,        /* 521 : TINT105       */
    Userdef_INTC_Dummy_Interrupt,        /* 522 : TINT106       */
    Userdef_INTC_Dummy_Interrupt,        /* 523 : TINT107       */
    Userdef_INTC_Dummy_Interrupt,        /* 524 : TINT108       */
    Userdef_INTC_Dummy_Interrupt,        /* 525 : TINT109       */
    Userdef_INTC_Dummy_Interrupt,        /* 526 : TINT110       */
    Userdef_INTC_Dummy_Interrupt,        /* 527 : TINT111       */
    Userdef_INTC_Dummy_Interrupt,        /* 528 : TINT112       */
    Userdef_INTC_Dummy_Interrupt,        /* 529 : TINT113       */
    Userdef_INTC_Dummy_Interrupt,        /* 530 : TINT114       */
    Userdef_INTC_Dummy_Interrupt,        /* 531 : TINT115       */
    Userdef_INTC_Dummy_Interrupt,        /* 532 : TINT116       */
    Userdef_INTC_Dummy_Interrupt,        /* 533 : TINT117       */
    Userdef_INTC_Dummy_Interrupt,        /* 534 : TINT118       */
    Userdef_INTC_Dummy_Interrupt,        /* 535 : TINT119       */
    Userdef_INTC_Dummy_Interrupt,        /* 536 : TINT120       */
    Userdef_INTC_Dummy_Interrupt,        /* 537 : TINT121       */
    Userdef_INTC_Dummy_Interrupt,        /* 538 : TINT122       */
    Userdef_INTC_Dummy_Interrupt,        /* 539 : TINT123       */
    Userdef_INTC_Dummy_Interrupt,        /* 540 : TINT124       */
    Userdef_INTC_Dummy_Interrupt,        /* 541 : TINT125       */
    Userdef_INTC_Dummy_Interrupt,        /* 542 : TINT126       */
    Userdef_INTC_Dummy_Interrupt,        /* 543 : TINT127       */
    Userdef_INTC_Dummy_Interrupt,        /* 544 : TINT128       */
    Userdef_INTC_Dummy_Interrupt,        /* 545 : TINT129       */
    Userdef_INTC_Dummy_Interrupt,        /* 546 : TINT130       */
    Userdef_INTC_Dummy_Interrupt,        /* 547 : TINT131       */
    Userdef_INTC_Dummy_Interrupt,        /* 548 : TINT132       */
    Userdef_INTC_Dummy_Interrupt,        /* 549 : TINT133       */
    Userdef_INTC_Dummy_Interrupt,        /* 550 : TINT134       */
    Userdef_INTC_Dummy_Interrupt,        /* 551 : TINT135       */
    Userdef_INTC_Dummy_Interrupt,        /* 552 : TINT136       */
    Userdef_INTC_Dummy_Interrupt,        /* 553 : TINT137       */
    Userdef_INTC_Dummy_Interrupt,        /* 554 : TINT138       */
    Userdef_INTC_Dummy_Interrupt,        /* 555 : TINT139       */
    Userdef_INTC_Dummy_Interrupt,        /* 556 : TINT140       */
    Userdef_INTC_Dummy_Interrupt,        /* 557 : TINT141       */
    Userdef_INTC_Dummy_Interrupt,        /* 558 : TINT142       */
    Userdef_INTC_Dummy_Interrupt,        /* 559 : TINT143       */
    Userdef_INTC_Dummy_Interrupt,        /* 560 : TINT144       */
    Userdef_INTC_Dummy_Interrupt,        /* 561 : TINT145       */
    Userdef_INTC_Dummy_Interrupt,        /* 562 : TINT146       */
    Userdef_INTC_Dummy_Interrupt,        /* 563 : TINT147       */
    Userdef_INTC_Dummy_Interrupt,        /* 564 : TINT148       */
    Userdef_INTC_Dummy_Interrupt,        /* 565 : TINT149       */
    Userdef_INTC_Dummy_Interrupt,        /* 566 : TINT150       */
    Userdef_INTC_Dummy_Interrupt,        /* 567 : TINT151       */
    Userdef_INTC_Dummy_Interrupt,        /* 568 : TINT152       */
    Userdef_INTC_Dummy_Interrupt,        /* 569 : TINT153       */
    Userdef_INTC_Dummy_Interrupt,        /* 570 : TINT154       */
    Userdef_INTC_Dummy_Interrupt,        /* 571 : TINT155       */
    Userdef_INTC_Dummy_Interrupt,        /* 572 : TINT156       */
    Userdef_INTC_Dummy_Interrupt,        /* 573 : TINT157       */
    Userdef_INTC_Dummy_Interrupt,        /* 574 : TINT158       */
    Userdef_INTC_Dummy_Interrupt,        /* 575 : TINT159       */
    Userdef_INTC_Dummy_Interrupt,        /* 576 : TINT160       */
    Userdef_INTC_Dummy_Interrupt,        /* 577 : TINT161       */
    Userdef_INTC_Dummy_Interrupt,        /* 578 : TINT162       */
    Userdef_INTC_Dummy_Interrupt,        /* 579 : TINT163       */
    Userdef_INTC_Dummy_Interrupt,        /* 580 : TINT164       */
    Userdef_INTC_Dummy_Interrupt,        /* 581 : TINT165       */
    Userdef_INTC_Dummy_Interrupt,        /* 582 : TINT166       */
    Userdef_INTC_Dummy_Interrupt,        /* 583 : TINT167       */
    Userdef_INTC_Dummy_Interrupt,        /* 584 : TINT168       */
    Userdef_INTC_Dummy_Interrupt,        /* 585 : TINT169       */
    Userdef_INTC_Dummy_Interrupt,        /* 586 : TINT170       */
};


/******************************************************************************
* Function Name: Userdef_INTC_RegistIntFunc
* Description  :
* Arguments    : uint16_t int_id
*              : void (* func)(uint32_t)
* Return Value : none
******************************************************************************/
void Userdef_INTC_RegistIntFunc(uint16_t int_id, void (* func)(uint32_t int_sense))
{
    intc_func_table[int_id] = func;
}

/******************************************************************************
* Function Name: Userdef_INTC_UndefId
* Description  :
* Arguments    : uint16_t int_id
* Return Value : none
******************************************************************************/
void Userdef_INTC_UndefId(uint16_t int_id)
{
    while (1)
    {
        /* Do Nothing */
    }
}

/******************************************************************************
* Function Name: Userdef_INTC_Dummy_Interrupt
* Description  :
* Arguments    : none
* Return Value : none
******************************************************************************/
static void Userdef_INTC_Dummy_Interrupt(uint32_t int_sense)
{
    /* Do Nothing */
}

/******************************************************************************
* Function Name: Userdef_FIQ_HandlerExe
* Description  :
* Arguments    : none
* Return Value : none
******************************************************************************/
void Userdef_FIQ_HandlerExe(void)
{
}

/* The function called by the RTOS port layer after it has managed interrupt
entry. */
void vApplicationIRQHandler( uint32_t ulICCIAR )
{
uint32_t ulInterruptID;

	/* Re-enable interrupts. */
    __enable_irq();

	/* The ID of the interrupt can be obtained by bitwise anding the ICCIAR value
	with 0x3FF. */
	ulInterruptID = ulICCIAR & 0x3FFUL;

	/* Call the function installed in the array of installed handler functions. */
	intc_func_table[ ulInterruptID ]( 0 );
}


/* END of File */

