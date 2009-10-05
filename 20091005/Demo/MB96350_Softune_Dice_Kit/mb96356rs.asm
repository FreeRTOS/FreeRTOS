/* FFMC-16 IO-MAP HEADER FILE                                                */
/* ==========================                                                */
/* CREATED BY IO-WIZARD V2.28                                                */
/* $Id: mb96356rs.asm,v 1.8 2008/02/28 09:05:44 mwilla Exp $ */
/* THIS SAMPLE CODE IS PROVIDED AS IS AND IS SUBJECT TO ALTERATIONS. FUJITSU */
/* MICROELECTRONICS ACCEPTS NO RESPONSIBILITY OR LIABILITY FOR ANY ERRORS OR */
/* ELIGIBILITY FOR ANY PURPOSES.                                             */
/*                 (C) Fujitsu Microelectronics Europe GmbH                  */
/* ************************************************************************* */
/*               FUJITSU MICROELECTRONICS EUROPE GMBH                        */
/*               Pittlerstrasse 47, 63225 Langen, Germany                    */
/*               Tel.:++49/6103/690-0,Fax - 122                              */
/*                                                                           */
/* The following software is for demonstration purposes only.                */
/* It is not fully tested, nor validated in order to fullfill                */
/* its task under all circumstances. Therefore, this software                */
/* or any part of it must only be used in an evaluation                      */
/* laboratory environment.                                                   */
/* This software is subject to the rules of our standard                     */
/* DISCLAIMER, that is delivered with our SW-tools on the CD or DVD          */
/* "Micros Documentation & Software" (V3.4 or later) or                      */
/* see our Internet Page -                                                   */
/* http://emea.fujitsu.com/microelectronics                                  */
/* ************************************************************************* */
/*                                                                           */
/* NOTE:                                                                     */
/*                                                                           */
/* This header-file covers all features of the chip MB96F356RS.              */
/*                                                                           */
/*                                                                           */
/* ----------------------------------------------------------------------    */
/* History:                                                                  */
/* Date        Version  Author  Description                                  */
/* 14.03.2007   1.0     MEf     Initial Release: reduced super-set           */
/*                              headerfile of MB96F348 to cover only the     */
/* 12.04.2007   1.2     Mef     Added Voltage Regulator Control Register     */
/*                              Added RD19V bit in Flash Memory Control      */
/*                              Status Register                              */
/* 21.09.2007   1.3     MWi     Completely revised version                   */
/* 17.10.2007   1.4     MWi     ADECR:LSEL, ADECR:HSEL removed               */
/* 26.02.2008   1.5     MWi     Flash control registers changed (Flash A/B)  */
/* 28.02.2008   1.6     MWi     Missing DDR05_D6 register added              */

 .PROGRAM MB96356RS
 .TITLE   MB96356RS

;-------------------------
; Function-Call Interface:
;-------------------------
#if __REG_PASS__
	.REG_PASS
#endif

;------------------------
; IO-AREA DEFINITIONS :
;------------------------



 .section IOBASE, IO, locate=0x0  ;
 .GLOBAL __pdr00,    __pdr01,    __pdr02,    __pdr03,    __pdr04,    __pdr05
 .GLOBAL __pdr06,    __adcs,     __adcsl,    __adcsh,    __adcr,     __adcrl
 .GLOBAL __adcrh,    __adsr,     __adecr,    __tcdt0,    __tccs0,    __tccsl0
 .GLOBAL __tccsh0,   __tcdt1,    __tccs1,    __tccsl1,   __tccsh1,   __ocs4
 .GLOBAL __ocs5,     __occp4,    __occp5,    __ocs6,     __ocs7,     __occp6
 .GLOBAL __occp7,    __ics01,    __ice01,    __ipcp0,    __ipcpl0,   __ipcph0
 .GLOBAL __ipcp1,    __ipcpl1,   __ipcph1,   __ics45,    __ice45,    __ipcp4
 .GLOBAL __ipcpl4,   __ipcph4,   __ipcp5,    __ipcpl5,   __ipcph5,   __ics67
 .GLOBAL __ice67,    __ipcp6,    __ipcpl6,   __ipcph6,   __ipcp7,    __ipcpl7
 .GLOBAL __ipcph7,   __enir0,    __eirr0,    __elvr0,    __elvrl0,   __elvrh0
 .GLOBAL __enir1,    __eirr1,    __elvr1,    __elvrl1,   __elvrh1,   __tmcsr0
 .GLOBAL __tmcsrl0,  __tmcsrh0,  __tmrlr0,   __tmr0,     __tmcsr1,   __tmcsrl1
 .GLOBAL __tmcsrh1,  __tmrlr1,   __tmr1,     __tmcsr2,   __tmcsrl2,  __tmcsrh2
 .GLOBAL __tmrlr2,   __tmr2,     __tmcsr3,   __tmcsrl3,  __tmcsrh3,  __tmrlr3
 .GLOBAL __tmr3,     __tmcsr6,   __tmcsrl6,  __tmcsrh6,  __tmrlr6,   __tmr6
 .GLOBAL __gcn10,    __gcn1l0,   __gcn1h0,   __gcn20,    __gcn2l0,   __gcn2h0
 .GLOBAL __ptmr0,    __pcsr0,    __pdut0,    __pcn0,     __pcnl0,    __pcnh0
 .GLOBAL __ptmr1,    __pcsr1,    __pdut1,    __pcn1,     __pcnl1,    __pcnh1
 .GLOBAL __ptmr2,    __pcsr2,    __pdut2,    __pcn2,     __pcnl2,    __pcnh2
 .GLOBAL __ptmr3,    __pcsr3,    __pdut3,    __pcn3,     __pcnl3,    __pcnh3
 .GLOBAL __gcn11,    __gcn1l1,   __gcn1h1,   __gcn21,    __gcn2l1,   __gcn2h1
 .GLOBAL __ptmr4,    __pcsr4,    __pdut4,    __pcn4,     __pcnl4,    __pcnh4
 .GLOBAL __ptmr5,    __pcsr5,    __pdut5,    __pcn5,     __pcnl5,    __pcnh5
 .GLOBAL __ibsr0,    __ibcr0,    __itba0,    __itbal0,   __itbah0,   __itmk0
 .GLOBAL __itmkl0,   __itmkh0,   __isba0,    __ismk0,    __idar0,    __iccr0
 .GLOBAL __smr2,     __scr2,     __tdr2,     __rdr2,     __ssr2,     __eccr2
 .GLOBAL __escr2,    __bgr2,     __bgrl2,    __bgrh2,    __esir2,    __smr3
 .GLOBAL __scr3,     __tdr3,     __rdr3,     __ssr3,     __eccr3,    __escr3
 .GLOBAL __bgr3,     __bgrl3,    __bgrh3,    __esir3

__pdr00   .res.b 1             ;000000
PDR00    .equ 0x0000
__pdr01   .res.b 1             ;000001
PDR01    .equ 0x0001
__pdr02   .res.b 1             ;000002
PDR02    .equ 0x0002
__pdr03   .res.b 1             ;000003
PDR03    .equ 0x0003
__pdr04   .res.b 1             ;000004
PDR04    .equ 0x0004
__pdr05   .res.b 1             ;000005
PDR05    .equ 0x0005
__pdr06   .res.b 1             ;000006
PDR06    .equ 0x0006
 .org 0x000018
__adcs  ; overlay symbol      ;000018
ADCS    .equ 0x0018
__adcsl   .res.b 1             ;000018
ADCSL    .equ 0x0018
__adcsh   .res.b 1             ;000019
ADCSH    .equ 0x0019
__adcr  ; overlay symbol      ;00001A
ADCR    .equ 0x001A
__adcrl   .res.b 1             ;00001A
ADCRL    .equ 0x001A
__adcrh   .res.b 1             ;00001B
ADCRH    .equ 0x001B
__adsr   .res.b 2             ;00001C
ADSR    .equ 0x001C
__adecr   .res.b 1             ;00001E
ADECR    .equ 0x001E
 .org 0x000020
__tcdt0   .res.b 2             ;000020
TCDT0    .equ 0x0020
__tccs0  ; overlay symbol      ;000022
TCCS0    .equ 0x0022
__tccsl0   .res.b 1             ;000022
TCCSL0    .equ 0x0022
__tccsh0   .res.b 1             ;000023
TCCSH0    .equ 0x0023
__tcdt1   .res.b 2             ;000024
TCDT1    .equ 0x0024
__tccs1  ; overlay symbol      ;000026
TCCS1    .equ 0x0026
__tccsl1   .res.b 1             ;000026
TCCSL1    .equ 0x0026
__tccsh1   .res.b 1             ;000027
TCCSH1    .equ 0x0027
 .org 0x000034
__ocs4   .res.b 1             ;000034
OCS4    .equ 0x0034
__ocs5   .res.b 1             ;000035
OCS5    .equ 0x0035
__occp4   .res.b 2             ;000036
OCCP4    .equ 0x0036
__occp5   .res.b 2             ;000038
OCCP5    .equ 0x0038
__ocs6   .res.b 1             ;00003A
OCS6    .equ 0x003A
__ocs7   .res.b 1             ;00003B
OCS7    .equ 0x003B
__occp6   .res.b 2             ;00003C
OCCP6    .equ 0x003C
__occp7   .res.b 2             ;00003E
OCCP7    .equ 0x003E
__ics01   .res.b 1             ;000040
ICS01    .equ 0x0040
__ice01   .res.b 1             ;000041
ICE01    .equ 0x0041
__ipcp0  ; overlay symbol      ;000042
IPCP0    .equ 0x0042
__ipcpl0   .res.b 1             ;000042
IPCPL0    .equ 0x0042
__ipcph0   .res.b 1             ;000043
IPCPH0    .equ 0x0043
__ipcp1  ; overlay symbol      ;000044
IPCP1    .equ 0x0044
__ipcpl1   .res.b 1             ;000044
IPCPL1    .equ 0x0044
__ipcph1   .res.b 1             ;000045
IPCPH1    .equ 0x0045
 .org 0x00004c
__ics45   .res.b 1             ;00004C
ICS45    .equ 0x004C
__ice45   .res.b 1             ;00004D
ICE45    .equ 0x004D
__ipcp4  ; overlay symbol      ;00004E
IPCP4    .equ 0x004E
__ipcpl4   .res.b 1             ;00004E
IPCPL4    .equ 0x004E
__ipcph4   .res.b 1             ;00004F
IPCPH4    .equ 0x004F
__ipcp5  ; overlay symbol      ;000050
IPCP5    .equ 0x0050
__ipcpl5   .res.b 1             ;000050
IPCPL5    .equ 0x0050
__ipcph5   .res.b 1             ;000051
IPCPH5    .equ 0x0051
__ics67   .res.b 1             ;000052
ICS67    .equ 0x0052
__ice67   .res.b 1             ;000053
ICE67    .equ 0x0053
__ipcp6  ; overlay symbol      ;000054
IPCP6    .equ 0x0054
__ipcpl6   .res.b 1             ;000054
IPCPL6    .equ 0x0054
__ipcph6   .res.b 1             ;000055
IPCPH6    .equ 0x0055
__ipcp7  ; overlay symbol      ;000056
IPCP7    .equ 0x0056
__ipcpl7   .res.b 1             ;000056
IPCPL7    .equ 0x0056
__ipcph7   .res.b 1             ;000057
IPCPH7    .equ 0x0057
__enir0   .res.b 1             ;000058
ENIR0    .equ 0x0058
__eirr0   .res.b 1             ;000059
EIRR0    .equ 0x0059
__elvr0  ; overlay symbol      ;00005A
ELVR0    .equ 0x005A
__elvrl0   .res.b 1             ;00005A
ELVRL0    .equ 0x005A
__elvrh0   .res.b 1             ;00005B
ELVRH0    .equ 0x005B
__enir1   .res.b 1             ;00005C
ENIR1    .equ 0x005C
__eirr1   .res.b 1             ;00005D
EIRR1    .equ 0x005D
__elvr1  ; overlay symbol      ;00005E
ELVR1    .equ 0x005E
__elvrl1   .res.b 1             ;00005E
ELVRL1    .equ 0x005E
__elvrh1   .res.b 1             ;00005F
ELVRH1    .equ 0x005F
__tmcsr0  ; overlay symbol      ;000060
TMCSR0    .equ 0x0060
__tmcsrl0   .res.b 1             ;000060
TMCSRL0    .equ 0x0060
__tmcsrh0   .res.b 1             ;000061
TMCSRH0    .equ 0x0061
__tmrlr0  ; overlay symbol      ;000062
TMRLR0    .equ 0x0062
__tmr0   .res.b 2             ;000062
TMR0    .equ 0x0062
__tmcsr1  ; overlay symbol      ;000064
TMCSR1    .equ 0x0064
__tmcsrl1   .res.b 1             ;000064
TMCSRL1    .equ 0x0064
__tmcsrh1   .res.b 1             ;000065
TMCSRH1    .equ 0x0065
__tmrlr1  ; overlay symbol      ;000066
TMRLR1    .equ 0x0066
__tmr1   .res.b 2             ;000066
TMR1    .equ 0x0066
__tmcsr2  ; overlay symbol      ;000068
TMCSR2    .equ 0x0068
__tmcsrl2   .res.b 1             ;000068
TMCSRL2    .equ 0x0068
__tmcsrh2   .res.b 1             ;000069
TMCSRH2    .equ 0x0069
__tmrlr2  ; overlay symbol      ;00006A
TMRLR2    .equ 0x006A
__tmr2   .res.b 2             ;00006A
TMR2    .equ 0x006A
__tmcsr3  ; overlay symbol      ;00006C
TMCSR3    .equ 0x006C
__tmcsrl3   .res.b 1             ;00006C
TMCSRL3    .equ 0x006C
__tmcsrh3   .res.b 1             ;00006D
TMCSRH3    .equ 0x006D
__tmrlr3  ; overlay symbol      ;00006E
TMRLR3    .equ 0x006E
__tmr3   .res.b 2             ;00006E
TMR3    .equ 0x006E
__tmcsr6  ; overlay symbol      ;000070
TMCSR6    .equ 0x0070
__tmcsrl6   .res.b 1             ;000070
TMCSRL6    .equ 0x0070
__tmcsrh6   .res.b 1             ;000071
TMCSRH6    .equ 0x0071
__tmrlr6  ; overlay symbol      ;000072
TMRLR6    .equ 0x0072
__tmr6   .res.b 2             ;000072
TMR6    .equ 0x0072
__gcn10  ; overlay symbol      ;000074
GCN10    .equ 0x0074
__gcn1l0   .res.b 1             ;000074
GCN1L0    .equ 0x0074
__gcn1h0   .res.b 1             ;000075
GCN1H0    .equ 0x0075
__gcn20  ; overlay symbol      ;000076
GCN20    .equ 0x0076
__gcn2l0   .res.b 1             ;000076
GCN2L0    .equ 0x0076
__gcn2h0   .res.b 1             ;000077
GCN2H0    .equ 0x0077
__ptmr0   .res.b 2             ;000078
PTMR0    .equ 0x0078
__pcsr0   .res.b 2             ;00007A
PCSR0    .equ 0x007A
__pdut0   .res.b 2             ;00007C
PDUT0    .equ 0x007C
__pcn0  ; overlay symbol      ;00007E
PCN0    .equ 0x007E
__pcnl0   .res.b 1             ;00007E
PCNL0    .equ 0x007E
__pcnh0   .res.b 1             ;00007F
PCNH0    .equ 0x007F
__ptmr1   .res.b 2             ;000080
PTMR1    .equ 0x0080
__pcsr1   .res.b 2             ;000082
PCSR1    .equ 0x0082
__pdut1   .res.b 2             ;000084
PDUT1    .equ 0x0084
__pcn1  ; overlay symbol      ;000086
PCN1    .equ 0x0086
__pcnl1   .res.b 1             ;000086
PCNL1    .equ 0x0086
__pcnh1   .res.b 1             ;000087
PCNH1    .equ 0x0087
__ptmr2   .res.b 2             ;000088
PTMR2    .equ 0x0088
__pcsr2   .res.b 2             ;00008A
PCSR2    .equ 0x008A
__pdut2   .res.b 2             ;00008C
PDUT2    .equ 0x008C
__pcn2  ; overlay symbol      ;00008E
PCN2    .equ 0x008E
__pcnl2   .res.b 1             ;00008E
PCNL2    .equ 0x008E
__pcnh2   .res.b 1             ;00008F
PCNH2    .equ 0x008F
__ptmr3   .res.b 2             ;000090
PTMR3    .equ 0x0090
__pcsr3   .res.b 2             ;000092
PCSR3    .equ 0x0092
__pdut3   .res.b 2             ;000094
PDUT3    .equ 0x0094
__pcn3  ; overlay symbol      ;000096
PCN3    .equ 0x0096
__pcnl3   .res.b 1             ;000096
PCNL3    .equ 0x0096
__pcnh3   .res.b 1             ;000097
PCNH3    .equ 0x0097
__gcn11  ; overlay symbol      ;000098
GCN11    .equ 0x0098
__gcn1l1   .res.b 1             ;000098
GCN1L1    .equ 0x0098
__gcn1h1   .res.b 1             ;000099
GCN1H1    .equ 0x0099
__gcn21  ; overlay symbol      ;00009A
GCN21    .equ 0x009A
__gcn2l1   .res.b 1             ;00009A
GCN2L1    .equ 0x009A
__gcn2h1   .res.b 1             ;00009B
GCN2H1    .equ 0x009B
__ptmr4   .res.b 2             ;00009C
PTMR4    .equ 0x009C
__pcsr4   .res.b 2             ;00009E
PCSR4    .equ 0x009E
__pdut4   .res.b 2             ;0000A0
PDUT4    .equ 0x00A0
__pcn4  ; overlay symbol      ;0000A2
PCN4    .equ 0x00A2
__pcnl4   .res.b 1             ;0000A2
PCNL4    .equ 0x00A2
__pcnh4   .res.b 1             ;0000A3
PCNH4    .equ 0x00A3
__ptmr5   .res.b 2             ;0000A4
PTMR5    .equ 0x00A4
__pcsr5   .res.b 2             ;0000A6
PCSR5    .equ 0x00A6
__pdut5   .res.b 2             ;0000A8
PDUT5    .equ 0x00A8
__pcn5  ; overlay symbol      ;0000AA
PCN5    .equ 0x00AA
__pcnl5   .res.b 1             ;0000AA
PCNL5    .equ 0x00AA
__pcnh5   .res.b 1             ;0000AB
PCNH5    .equ 0x00AB
__ibsr0   .res.b 1             ;0000AC
IBSR0    .equ 0x00AC
__ibcr0   .res.b 1             ;0000AD
IBCR0    .equ 0x00AD
__itba0  ; overlay symbol      ;0000AE
ITBA0    .equ 0x00AE
__itbal0   .res.b 1             ;0000AE
ITBAL0    .equ 0x00AE
__itbah0   .res.b 1             ;0000AF
ITBAH0    .equ 0x00AF
__itmk0  ; overlay symbol      ;0000B0
ITMK0    .equ 0x00B0
__itmkl0   .res.b 1             ;0000B0
ITMKL0    .equ 0x00B0
__itmkh0   .res.b 1             ;0000B1
ITMKH0    .equ 0x00B1
__isba0   .res.b 1             ;0000B2
ISBA0    .equ 0x00B2
__ismk0   .res.b 1             ;0000B3
ISMK0    .equ 0x00B3
__idar0   .res.b 1             ;0000B4
IDAR0    .equ 0x00B4
__iccr0   .res.b 1             ;0000B5
ICCR0    .equ 0x00B5
 .org 0x0000d4
__smr2   .res.b 1             ;0000D4
SMR2    .equ 0x00D4
__scr2   .res.b 1             ;0000D5
SCR2    .equ 0x00D5
__tdr2  ; overlay symbol      ;0000D6
TDR2    .equ 0x00D6
__rdr2   .res.b 1             ;0000D6
RDR2    .equ 0x00D6
__ssr2   .res.b 1             ;0000D7
SSR2    .equ 0x00D7
__eccr2   .res.b 1             ;0000D8
ECCR2    .equ 0x00D8
__escr2   .res.b 1             ;0000D9
ESCR2    .equ 0x00D9
__bgr2  ; overlay symbol      ;0000DA
BGR2    .equ 0x00DA
__bgrl2   .res.b 1             ;0000DA
BGRL2    .equ 0x00DA
__bgrh2   .res.b 1             ;0000DB
BGRH2    .equ 0x00DB
__esir2   .res.b 1             ;0000DC
ESIR2    .equ 0x00DC
 .org 0x0000de
__smr3   .res.b 1             ;0000DE
SMR3    .equ 0x00DE
__scr3   .res.b 1             ;0000DF
SCR3    .equ 0x00DF
__tdr3  ; overlay symbol      ;0000E0
TDR3    .equ 0x00E0
__rdr3   .res.b 1             ;0000E0
RDR3    .equ 0x00E0
__ssr3   .res.b 1             ;0000E1
SSR3    .equ 0x00E1
__eccr3   .res.b 1             ;0000E2
ECCR3    .equ 0x00E2
__escr3   .res.b 1             ;0000E3
ESCR3    .equ 0x00E3
__bgr3  ; overlay symbol      ;0000E4
BGR3    .equ 0x00E4
__bgrl3   .res.b 1             ;0000E4
BGRL3    .equ 0x00E4
__bgrh3   .res.b 1             ;0000E5
BGRH3    .equ 0x00E5
__esir3   .res.b 1             ;0000E6
ESIR3    .equ 0x00E6

 .section DMADESCRIPTOR, DATA, locate=0x100  ;
 .GLOBAL __bapl0,    __bapm0,    __baph0,    __dmacs0,   __ioa0,     __ioal0
 .GLOBAL __ioah0,    __dct0,     __dctl0,    __dcth0,    __bapl1,    __bapm1
 .GLOBAL __baph1,    __dmacs1,   __ioa1,     __ioal1,    __ioah1,    __dct1
 .GLOBAL __dctl1,    __dcth1,    __bapl2,    __bapm2,    __baph2,    __dmacs2
 .GLOBAL __ioa2,     __ioal2,    __ioah2,    __dct2,     __dctl2,    __dcth2
 .GLOBAL __bapl3,    __bapm3,    __baph3,    __dmacs3,   __ioa3,     __ioal3
 .GLOBAL __ioah3,    __dct3,     __dctl3,    __dcth3

__bapl0   .res.b 1             ;000100
BAPL0    .equ 0x0100
__bapm0   .res.b 1             ;000101
BAPM0    .equ 0x0101
__baph0   .res.b 1             ;000102
BAPH0    .equ 0x0102
__dmacs0   .res.b 1             ;000103
DMACS0    .equ 0x0103
__ioa0  ; overlay symbol      ;000104
IOA0    .equ 0x0104
__ioal0   .res.b 1             ;000104
IOAL0    .equ 0x0104
__ioah0   .res.b 1             ;000105
IOAH0    .equ 0x0105
__dct0  ; overlay symbol      ;000106
DCT0    .equ 0x0106
__dctl0   .res.b 1             ;000106
DCTL0    .equ 0x0106
__dcth0   .res.b 1             ;000107
DCTH0    .equ 0x0107
__bapl1   .res.b 1             ;000108
BAPL1    .equ 0x0108
__bapm1   .res.b 1             ;000109
BAPM1    .equ 0x0109
__baph1   .res.b 1             ;00010A
BAPH1    .equ 0x010A
__dmacs1   .res.b 1             ;00010B
DMACS1    .equ 0x010B
__ioa1  ; overlay symbol      ;00010C
IOA1    .equ 0x010C
__ioal1   .res.b 1             ;00010C
IOAL1    .equ 0x010C
__ioah1   .res.b 1             ;00010D
IOAH1    .equ 0x010D
__dct1  ; overlay symbol      ;00010E
DCT1    .equ 0x010E
__dctl1   .res.b 1             ;00010E
DCTL1    .equ 0x010E
__dcth1   .res.b 1             ;00010F
DCTH1    .equ 0x010F
__bapl2   .res.b 1             ;000110
BAPL2    .equ 0x0110
__bapm2   .res.b 1             ;000111
BAPM2    .equ 0x0111
__baph2   .res.b 1             ;000112
BAPH2    .equ 0x0112
__dmacs2   .res.b 1             ;000113
DMACS2    .equ 0x0113
__ioa2  ; overlay symbol      ;000114
IOA2    .equ 0x0114
__ioal2   .res.b 1             ;000114
IOAL2    .equ 0x0114
__ioah2   .res.b 1             ;000115
IOAH2    .equ 0x0115
__dct2  ; overlay symbol      ;000116
DCT2    .equ 0x0116
__dctl2   .res.b 1             ;000116
DCTL2    .equ 0x0116
__dcth2   .res.b 1             ;000117
DCTH2    .equ 0x0117
__bapl3   .res.b 1             ;000118
BAPL3    .equ 0x0118
__bapm3   .res.b 1             ;000119
BAPM3    .equ 0x0119
__baph3   .res.b 1             ;00011A
BAPH3    .equ 0x011A
__dmacs3   .res.b 1             ;00011B
DMACS3    .equ 0x011B
__ioa3  ; overlay symbol      ;00011C
IOA3    .equ 0x011C
__ioal3   .res.b 1             ;00011C
IOAL3    .equ 0x011C
__ioah3   .res.b 1             ;00011D
IOAH3    .equ 0x011D
__dct3  ; overlay symbol      ;00011E
DCT3    .equ 0x011E
__dctl3   .res.b 1             ;00011E
DCTL3    .equ 0x011E
__dcth3   .res.b 1             ;00011F
DCTH3    .equ 0x011F

 .section IOXTND, DATA, locate=0x380  ;
 .GLOBAL __disel0,   __disel1,   __disel2,   __disel3,   __dsr,      __dsrl
 .GLOBAL __dsrh,     __dssr,     __dssrl,    __dssrh,    __der,      __derl
 .GLOBAL __derh,     __icr,      __ilr,      __idx,      __tbr,      __tbrl
 .GLOBAL __tbrh,     __dirr,     __nmi,      __edsu2,    __romm,     __edsu
 .GLOBAL __pfcs0,    __pfcs1,    __pfcs2,    __pfcs3,    __pfal0,    __pfam0
 .GLOBAL __pfah0,    __pfal1,    __pfam1,    __pfah1,    __pfal2,    __pfam2
 .GLOBAL __pfah2,    __pfal3,    __pfam3,    __pfah3,    __pfal4,    __pfam4
 .GLOBAL __pfah4,    __pfal5,    __pfam5,    __pfah5,    __pfal6,    __pfam6
 .GLOBAL __pfah6,    __pfal7,    __pfam7,    __pfah7,    __pfd0,     __pfdl0
 .GLOBAL __pfdh0,    __pfd1,     __pfdl1,    __pfdh1,    __pfd2,     __pfdl2
 .GLOBAL __pfdh2,    __pfd3,     __pfdl3,    __pfdh3,    __pfd4,     __pfdl4
 .GLOBAL __pfdh4,    __pfd5,     __pfdl5,    __pfdh5,    __pfd6,     __pfdl6
 .GLOBAL __pfdh6,    __pfd7,     __pfdl7,    __pfdh7,    __mcsra,    __mtcra
 .GLOBAL __mtcral,   __mtcrah,   __fmwc1,    __fmwc2,    __fmwc3,    __fmwc4
 .GLOBAL __fmwc5,    __smcr,     __cksr,     __ckssr,    __ckmr,     __ckfcr
 .GLOBAL __ckfcrl,   __ckfcrh,   __pllcr,    __pllcrl,   __pllcrh,   __rctcr
 .GLOBAL __mctcr,    __rccsrc,   __rcr,      __rccsr,    __wdtc,     __wdtcp
 .GLOBAL __coar,     __cocr0,    __cocr1,    __cmcr,     __cmpr,     __cmprl
 .GLOBAL __cmprh,    __vrcr,     __ddr00,    __ddr01,    __ddr02,    __ddr03
 .GLOBAL __ddr04,    __ddr05,    __ddr06,    __pier00,   __pier01,   __pier02
 .GLOBAL __pier03,   __pier04,   __pier05,   __pier06,   __pilr00,   __pilr01
 .GLOBAL __pilr02,   __pilr03,   __pilr04,   __pilr05,   __pilr06,   __epilr00
 .GLOBAL __epilr01,  __epilr02,  __epilr03,  __epilr04,  __epilr05,  __epilr06
 .GLOBAL __podr00,   __podr01,   __podr02,   __podr03,   __podr04,   __podr05
 .GLOBAL __podr06,   __pucr00,   __pucr01,   __pucr02,   __pucr03,   __pucr04
 .GLOBAL __pucr05,   __pucr06,   __epsr00,   __epsr01,   __epsr02,   __epsr03
 .GLOBAL __epsr04,   __epsr05,   __epsr06,   __ader0,    __ader1,    __prrr0
 .GLOBAL __prrr1,    __prrr2,    __prrr3,    __prrr4,    __prrr5,    __prrr6
 .GLOBAL __prrr7,    __prrr8,    __prrr9,    __wtbr0,    __wtbrl0,   __wtbrh0
 .GLOBAL __wtbr1,    __wtsr,     __wtmr,     __wthr,     __wtcer,    __wtcksr
 .GLOBAL __wtcr,     __wtcrl,    __wtcrh,    __cucr,     __cutd,     __cutdl
 .GLOBAL __cutdh,    __cutr,     __cutr2,    __cutr2l,   __cutr2h,   __cutr1
 .GLOBAL __cutr1l,   __cutr1h,   __tmisr,    __tcdt2,    __tccs2,    __tccsl2
 .GLOBAL __tccsh2,   __tcdt3,    __tccs3,    __tccsl3,   __tccsh3,   __smr7
 .GLOBAL __scr7,     __tdr7,     __rdr7,     __ssr7,     __eccr7,    __escr7
 .GLOBAL __bgr7,     __bgrl7,    __bgrh7,    __esir7,    __smr8,     __scr8
 .GLOBAL __tdr8,     __rdr8,     __ssr8,     __eccr8,    __escr8,    __bgr8
 .GLOBAL __bgrl8,    __bgrh8,    __esir8,    __ptmr6,    __pcsr6,    __pdut6
 .GLOBAL __pcn6,     __pcnl6,    __pcnh6,    __ptmr7,    __pcsr7,    __pdut7
 .GLOBAL __pcn7,     __pcnl7,    __pcnh7,    __gcn12,    __gcn1l2,   __gcn1h2
 .GLOBAL __gcn22,    __gcn2l2,   __gcn2h2,   __ptmr8,    __pcsr8,    __pdut8
 .GLOBAL __pcn8,     __pcnl8,    __pcnh8,    __ptmr9,    __pcsr9,    __pdut9
 .GLOBAL __pcn9,     __pcnl9,    __pcnh9,    __ptmr10,   __pcsr10,   __pdut10
 .GLOBAL __pcn10,    __pcnl10,   __pcnh10,   __ptmr11,   __pcsr11,   __pdut11
 .GLOBAL __pcn11,    __pcnl11,   __pcnh11,   __gcn13,    __gcn1l3,   __gcn1h3
 .GLOBAL __gcn23,    __gcn2l3,   __gcn2h3,   __ptmr12,   __pcsr12,   __pdut12
 .GLOBAL __pcn12,    __pcnl12,   __pcnh12,   __ptmr13,   __pcsr13,   __pdut13
 .GLOBAL __pcn13,    __pcnl13,   __pcnh13,   __ptmr14,   __pcsr14,   __pdut14
 .GLOBAL __pcn14,    __pcnl14,   __pcnh14,   __ptmr15,   __pcsr15,   __pdut15
 .GLOBAL __pcn15,    __pcnl15,   __pcnh15,   __gcn14,    __gcn1l4,   __gcn1h4
 .GLOBAL __gcn24,    __gcn2l4,   __gcn2h4,   __ptmr16,   __pcsr16,   __pdut16
 .GLOBAL __pcn16,    __pcnl16,   __pcnh16,   __ptmr17,   __pcsr17,   __pdut17
 .GLOBAL __pcn17,    __pcnl17,   __pcnh17,   __ptmr18,   __pcsr18,   __pdut18
 .GLOBAL __pcn18,    __pcnl18,   __pcnh18,   __ptmr19,   __pcsr19,   __pdut19
 .GLOBAL __pcn19,    __pcnl19,   __pcnh19,   __prrr10,   __prrr11,   __prrr12
 .GLOBAL __prrr13,   __eac0,     __eacl0,    __each0,    __eac1,     __eacl1
 .GLOBAL __each1,    __eac2,     __eacl2,    __each2,    __eac3,     __eacl3
 .GLOBAL __each3,    __eac4,     __eacl4,    __each4,    __eac5,     __eacl5
 .GLOBAL __each5,    __eas2,     __eas3,     __eas4,     __eas5,     __ebm
 .GLOBAL __ebcf,     __ebae0,    __ebae1,    __ebae2,    __ebcs,     __ctrlr1
 .GLOBAL __ctrlrl1,  __ctrlrh1,  __statr1,   __statrl1,  __statrh1,  __errcnt1
 .GLOBAL __errcntl1, __errcnth1, __btr1,     __btrl1,    __btrh1,    __intr1
 .GLOBAL __intrl1,   __intrh1,   __testr1,   __testrl1,  __testrh1,  __brper1
 .GLOBAL __brperl1,  __brperh1,  __if1creq1, __if1creql1, __if1creqh1, __if1cmsk1
 .GLOBAL __if1cmskl1, __if1cmskh1, __if1msk1,  __if1msk11, __if1msk1l1, __if1msk1h1
 .GLOBAL __if1msk21, __if1msk2l1, __if1msk2h1, __if1arb1,  __if1arb11, __if1arb1l1
 .GLOBAL __if1arb1h1, __if1arb21, __if1arb2l1, __if1arb2h1, __if1mctr1, __if1mctrl1
 .GLOBAL __if1mctrh1, __if1dta1,  __if1dta11, __if1dta1l1, __if1dta1h1, __if1dta21
 .GLOBAL __if1dta2l1, __if1dta2h1, __if1dtb1,  __if1dtb11, __if1dtb1l1, __if1dtb1h1
 .GLOBAL __if1dtb21, __if1dtb2l1, __if1dtb2h1, __if2creq1, __if2creql1, __if2creqh1
 .GLOBAL __if2cmsk1, __if2cmskl1, __if2cmskh1, __if2msk1,  __if2msk11, __if2msk1l1
 .GLOBAL __if2msk1h1, __if2msk21, __if2msk2l1, __if2msk2h1, __if2arb1,  __if2arb11
 .GLOBAL __if2arb1l1, __if2arb1h1, __if2arb21, __if2arb2l1, __if2arb2h1, __if2mctr1
 .GLOBAL __if2mctrl1, __if2mctrh1, __if2dta1,  __if2dta11, __if2dta1l1, __if2dta1h1
 .GLOBAL __if2dta21, __if2dta2l1, __if2dta2h1, __if2dtb1,  __if2dtb11, __if2dtb1l1
 .GLOBAL __if2dtb1h1, __if2dtb21, __if2dtb2l1, __if2dtb2h1, __treqr1,   __treqr11
 .GLOBAL __treqr1l1, __treqr1h1, __treqr21,  __treqr2l1, __treqr2h1, __newdt1
 .GLOBAL __newdt11,  __newdt1l1, __newdt1h1, __newdt21,  __newdt2l1, __newdt2h1
 .GLOBAL __intpnd1,  __intpnd11, __intpnd1l1, __intpnd1h1, __intpnd21, __intpnd2l1
 .GLOBAL __intpnd2h1, __msgval1,  __msgval11, __msgval1l1, __msgval1h1, __msgval21
 .GLOBAL __msgval2l1, __msgval2h1, __coer1,    __ctrlr2,   __ctrlrl2,  __ctrlrh2
 .GLOBAL __statr2,   __statrl2,  __statrh2,  __errcnt2,  __errcntl2, __errcnth2
 .GLOBAL __btr2,     __btrl2,    __btrh2,    __intr2,    __intrl2,   __intrh2
 .GLOBAL __testr2,   __testrl2,  __testrh2,  __brper2,   __brperl2,  __brperh2
 .GLOBAL __if1creq2, __if1creql2, __if1creqh2, __if1cmsk2, __if1cmskl2, __if1cmskh2
 .GLOBAL __if1msk2,  __if1msk12, __if1msk1l2, __if1msk1h2, __if1msk22, __if1msk2l2
 .GLOBAL __if1msk2h2, __if1arb2,  __if1arb12, __if1arb1l2, __if1arb1h2, __if1arb22
 .GLOBAL __if1arb2l2, __if1arb2h2, __if1mctr2, __if1mctrl2, __if1mctrh2, __if1dta2
 .GLOBAL __if1dta12, __if1dta1l2, __if1dta1h2, __if1dta22, __if1dta2l2, __if1dta2h2
 .GLOBAL __if1dtb2,  __if1dtb12, __if1dtb1l2, __if1dtb1h2, __if1dtb22, __if1dtb2l2
 .GLOBAL __if1dtb2h2, __if2creq2, __if2creql2, __if2creqh2, __if2cmsk2, __if2cmskl2
 .GLOBAL __if2cmskh2, __if2msk2,  __if2msk12, __if2msk1l2, __if2msk1h2, __if2msk22
 .GLOBAL __if2msk2l2, __if2msk2h2, __if2arb2,  __if2arb12, __if2arb1l2, __if2arb1h2
 .GLOBAL __if2arb22, __if2arb2l2, __if2arb2h2, __if2mctr2, __if2mctrl2, __if2mctrh2
 .GLOBAL __if2dta2,  __if2dta12, __if2dta1l2, __if2dta1h2, __if2dta22, __if2dta2l2
 .GLOBAL __if2dta2h2, __if2dtb2,  __if2dtb12, __if2dtb1l2, __if2dtb1h2, __if2dtb22
 .GLOBAL __if2dtb2l2, __if2dtb2h2, __treqr2,   __treqr12,  __treqr1l2, __treqr1h2
 .GLOBAL __treqr22,  __treqr2l2, __treqr2h2, __newdt2,   __newdt12,  __newdt1l2
 .GLOBAL __newdt1h2, __newdt22,  __newdt2l2, __newdt2h2, __intpnd2,  __intpnd12
 .GLOBAL __intpnd1l2, __intpnd1h2, __intpnd22, __intpnd2l2, __intpnd2h2, __msgval2
 .GLOBAL __msgval12, __msgval1l2, __msgval1h2, __msgval22, __msgval2l2, __msgval2h2
 .GLOBAL __coer2

__disel0   .res.b 1             ;000380
DISEL0    .equ 0x0380
__disel1   .res.b 1             ;000381
DISEL1    .equ 0x0381
__disel2   .res.b 1             ;000382
DISEL2    .equ 0x0382
__disel3   .res.b 1             ;000383
DISEL3    .equ 0x0383
 .org 0x000390
__dsr  ; overlay symbol      ;000390
DSR    .equ 0x0390
__dsrl   .res.b 1             ;000390
DSRL    .equ 0x0390
__dsrh   .res.b 1             ;000391
DSRH    .equ 0x0391
__dssr  ; overlay symbol      ;000392
DSSR    .equ 0x0392
__dssrl   .res.b 1             ;000392
DSSRL    .equ 0x0392
__dssrh   .res.b 1             ;000393
DSSRH    .equ 0x0393
__der  ; overlay symbol      ;000394
DER    .equ 0x0394
__derl   .res.b 1             ;000394
DERL    .equ 0x0394
__derh   .res.b 1             ;000395
DERH    .equ 0x0395
 .org 0x0003a0
__icr  ; overlay symbol      ;0003A0
ICR    .equ 0x03A0
__ilr   .res.b 1             ;0003A0
ILR    .equ 0x03A0
__idx   .res.b 1             ;0003A1
IDX    .equ 0x03A1
__tbr  ; overlay symbol      ;0003A2
TBR    .equ 0x03A2
__tbrl   .res.b 1             ;0003A2
TBRL    .equ 0x03A2
__tbrh   .res.b 1             ;0003A3
TBRH    .equ 0x03A3
__dirr   .res.b 1             ;0003A4
DIRR    .equ 0x03A4
__nmi   .res.b 1             ;0003A5
NMI    .equ 0x03A5
 .org 0x0003ac
__edsu2   .res.b 2             ;0003AC
EDSU2    .equ 0x03AC
__romm   .res.b 1             ;0003AE
ROMM    .equ 0x03AE
__edsu   .res.b 1             ;0003AF
EDSU    .equ 0x03AF
__pfcs0   .res.b 2             ;0003B0
PFCS0    .equ 0x03B0
__pfcs1   .res.b 2             ;0003B2
PFCS1    .equ 0x03B2
__pfcs2   .res.b 2             ;0003B4
PFCS2    .equ 0x03B4
__pfcs3   .res.b 2             ;0003B6
PFCS3    .equ 0x03B6
__pfal0   .res.b 1             ;0003B8
PFAL0    .equ 0x03B8
__pfam0   .res.b 1             ;0003B9
PFAM0    .equ 0x03B9
__pfah0   .res.b 1             ;0003BA
PFAH0    .equ 0x03BA
__pfal1   .res.b 1             ;0003BB
PFAL1    .equ 0x03BB
__pfam1   .res.b 1             ;0003BC
PFAM1    .equ 0x03BC
__pfah1   .res.b 1             ;0003BD
PFAH1    .equ 0x03BD
__pfal2   .res.b 1             ;0003BE
PFAL2    .equ 0x03BE
__pfam2   .res.b 1             ;0003BF
PFAM2    .equ 0x03BF
__pfah2   .res.b 1             ;0003C0
PFAH2    .equ 0x03C0
__pfal3   .res.b 1             ;0003C1
PFAL3    .equ 0x03C1
__pfam3   .res.b 1             ;0003C2
PFAM3    .equ 0x03C2
__pfah3   .res.b 1             ;0003C3
PFAH3    .equ 0x03C3
__pfal4   .res.b 1             ;0003C4
PFAL4    .equ 0x03C4
__pfam4   .res.b 1             ;0003C5
PFAM4    .equ 0x03C5
__pfah4   .res.b 1             ;0003C6
PFAH4    .equ 0x03C6
__pfal5   .res.b 1             ;0003C7
PFAL5    .equ 0x03C7
__pfam5   .res.b 1             ;0003C8
PFAM5    .equ 0x03C8
__pfah5   .res.b 1             ;0003C9
PFAH5    .equ 0x03C9
__pfal6   .res.b 1             ;0003CA
PFAL6    .equ 0x03CA
__pfam6   .res.b 1             ;0003CB
PFAM6    .equ 0x03CB
__pfah6   .res.b 1             ;0003CC
PFAH6    .equ 0x03CC
__pfal7   .res.b 1             ;0003CD
PFAL7    .equ 0x03CD
__pfam7   .res.b 1             ;0003CE
PFAM7    .equ 0x03CE
__pfah7   .res.b 1             ;0003CF
PFAH7    .equ 0x03CF
__pfd0  ; overlay symbol      ;0003D0
PFD0    .equ 0x03D0
__pfdl0   .res.b 1             ;0003D0
PFDL0    .equ 0x03D0
__pfdh0   .res.b 1             ;0003D1
PFDH0    .equ 0x03D1
__pfd1  ; overlay symbol      ;0003D2
PFD1    .equ 0x03D2
__pfdl1   .res.b 1             ;0003D2
PFDL1    .equ 0x03D2
__pfdh1   .res.b 1             ;0003D3
PFDH1    .equ 0x03D3
__pfd2  ; overlay symbol      ;0003D4
PFD2    .equ 0x03D4
__pfdl2   .res.b 1             ;0003D4
PFDL2    .equ 0x03D4
__pfdh2   .res.b 1             ;0003D5
PFDH2    .equ 0x03D5
__pfd3  ; overlay symbol      ;0003D6
PFD3    .equ 0x03D6
__pfdl3   .res.b 1             ;0003D6
PFDL3    .equ 0x03D6
__pfdh3   .res.b 1             ;0003D7
PFDH3    .equ 0x03D7
__pfd4  ; overlay symbol      ;0003D8
PFD4    .equ 0x03D8
__pfdl4   .res.b 1             ;0003D8
PFDL4    .equ 0x03D8
__pfdh4   .res.b 1             ;0003D9
PFDH4    .equ 0x03D9
__pfd5  ; overlay symbol      ;0003DA
PFD5    .equ 0x03DA
__pfdl5   .res.b 1             ;0003DA
PFDL5    .equ 0x03DA
__pfdh5   .res.b 1             ;0003DB
PFDH5    .equ 0x03DB
__pfd6  ; overlay symbol      ;0003DC
PFD6    .equ 0x03DC
__pfdl6   .res.b 1             ;0003DC
PFDL6    .equ 0x03DC
__pfdh6   .res.b 1             ;0003DD
PFDH6    .equ 0x03DD
__pfd7  ; overlay symbol      ;0003DE
PFD7    .equ 0x03DE
__pfdl7   .res.b 1             ;0003DE
PFDL7    .equ 0x03DE
__pfdh7   .res.b 1             ;0003DF
PFDH7    .equ 0x03DF
 .org 0x0003f1
__mcsra   .res.b 1             ;0003F1
MCSRA    .equ 0x03F1
__mtcra  ; overlay symbol      ;0003F2
MTCRA    .equ 0x03F2
__mtcral   .res.b 1             ;0003F2
MTCRAL    .equ 0x03F2
__mtcrah   .res.b 1             ;0003F3
MTCRAH    .equ 0x03F3
 .org 0x0003f9
__fmwc1   .res.b 1             ;0003F9
FMWC1    .equ 0x03F9
__fmwc2   .res.b 1             ;0003FA
FMWC2    .equ 0x03FA
__fmwc3   .res.b 1             ;0003FB
FMWC3    .equ 0x03FB
__fmwc4   .res.b 1             ;0003FC
FMWC4    .equ 0x03FC
__fmwc5   .res.b 1             ;0003FD
FMWC5    .equ 0x03FD
 .org 0x000400
__smcr   .res.b 1             ;000400
SMCR    .equ 0x0400
__cksr   .res.b 1             ;000401
CKSR    .equ 0x0401
__ckssr   .res.b 1             ;000402
CKSSR    .equ 0x0402
__ckmr   .res.b 1             ;000403
CKMR    .equ 0x0403
__ckfcr  ; overlay symbol      ;000404
CKFCR    .equ 0x0404
__ckfcrl   .res.b 1             ;000404
CKFCRL    .equ 0x0404
__ckfcrh   .res.b 1             ;000405
CKFCRH    .equ 0x0405
__pllcr  ; overlay symbol      ;000406
PLLCR    .equ 0x0406
__pllcrl   .res.b 1             ;000406
PLLCRL    .equ 0x0406
__pllcrh   .res.b 1             ;000407
PLLCRH    .equ 0x0407
__rctcr   .res.b 1             ;000408
RCTCR    .equ 0x0408
__mctcr   .res.b 1             ;000409
MCTCR    .equ 0x0409
 .org 0x00040b
__rccsrc   .res.b 1             ;00040B
RCCSRC    .equ 0x040B
__rcr   .res.b 1             ;00040C
RCR    .equ 0x040C
__rccsr   .res.b 1             ;00040D
RCCSR    .equ 0x040D
__wdtc   .res.b 1             ;00040E
WDTC    .equ 0x040E
__wdtcp   .res.b 1             ;00040F
WDTCP    .equ 0x040F
 .org 0x000415
__coar   .res.b 1             ;000415
COAR    .equ 0x0415
__cocr0   .res.b 1             ;000416
COCR0    .equ 0x0416
__cocr1   .res.b 1             ;000417
COCR1    .equ 0x0417
__cmcr   .res.b 1             ;000418
CMCR    .equ 0x0418
 .org 0x00041a
__cmpr  ; overlay symbol      ;00041A
CMPR    .equ 0x041A
__cmprl   .res.b 1             ;00041A
CMPRL    .equ 0x041A
__cmprh   .res.b 1             ;00041B
CMPRH    .equ 0x041B
 .org 0x00042c
__vrcr   .res.b 1             ;00042C
VRCR    .equ 0x042C
 .org 0x000430
__ddr00   .res.b 1             ;000430
DDR00    .equ 0x0430
__ddr01   .res.b 1             ;000431
DDR01    .equ 0x0431
__ddr02   .res.b 1             ;000432
DDR02    .equ 0x0432
__ddr03   .res.b 1             ;000433
DDR03    .equ 0x0433
__ddr04   .res.b 1             ;000434
DDR04    .equ 0x0434
__ddr05   .res.b 1             ;000435
DDR05    .equ 0x0435
__ddr06   .res.b 1             ;000436
DDR06    .equ 0x0436
 .org 0x000444
__pier00   .res.b 1             ;000444
PIER00    .equ 0x0444
__pier01   .res.b 1             ;000445
PIER01    .equ 0x0445
__pier02   .res.b 1             ;000446
PIER02    .equ 0x0446
__pier03   .res.b 1             ;000447
PIER03    .equ 0x0447
__pier04   .res.b 1             ;000448
PIER04    .equ 0x0448
__pier05   .res.b 1             ;000449
PIER05    .equ 0x0449
__pier06   .res.b 1             ;00044A
PIER06    .equ 0x044A
 .org 0x000458
__pilr00   .res.b 1             ;000458
PILR00    .equ 0x0458
__pilr01   .res.b 1             ;000459
PILR01    .equ 0x0459
__pilr02   .res.b 1             ;00045A
PILR02    .equ 0x045A
__pilr03   .res.b 1             ;00045B
PILR03    .equ 0x045B
__pilr04   .res.b 1             ;00045C
PILR04    .equ 0x045C
__pilr05   .res.b 1             ;00045D
PILR05    .equ 0x045D
__pilr06   .res.b 1             ;00045E
PILR06    .equ 0x045E
 .org 0x00046C
__epilr00   .res.b 1             ;00046C
EPILR00    .equ 0x046C
__epilr01   .res.b 1             ;00046D
EPILR01    .equ 0x046D
__epilr02   .res.b 1             ;00046E
EPILR02    .equ 0x046E
__epilr03   .res.b 1             ;00046F
EPILR03    .equ 0x046F
__epilr04   .res.b 1             ;000470
EPILR04    .equ 0x0470
__epilr05   .res.b 1             ;000471
EPILR05    .equ 0x0471
__epilr06   .res.b 1             ;000472
EPILR06    .equ 0x0472
 .org 0x000480
__podr00   .res.b 1             ;000480
PODR00    .equ 0x0480
__podr01   .res.b 1             ;000481
PODR01    .equ 0x0481
__podr02   .res.b 1             ;000482
PODR02    .equ 0x0482
__podr03   .res.b 1             ;000483
PODR03    .equ 0x0483
__podr04   .res.b 1             ;000484
PODR04    .equ 0x0484
__podr05   .res.b 1             ;000485
PODR05    .equ 0x0485
__podr06   .res.b 1             ;000486
PODR06    .equ 0x0486
 .org 0x0004A8
__pucr00   .res.b 1             ;0004A8
PUCR00    .equ 0x04A8
__pucr01   .res.b 1             ;0004A9
PUCR01    .equ 0x04A9
__pucr02   .res.b 1             ;0004AA
PUCR02    .equ 0x04AA
__pucr03   .res.b 1             ;0004AB
PUCR03    .equ 0x04AB
__pucr04   .res.b 1             ;0004AC
PUCR04    .equ 0x04AC
__pucr05   .res.b 1             ;0004AD
PUCR05    .equ 0x04AD
__pucr06   .res.b 1             ;0004AE
PUCR06    .equ 0x04AE
 .org 0x0004BC
__epsr00   .res.b 1             ;0004BC
EPSR00    .equ 0x04BC
__epsr01   .res.b 1             ;0004BD
EPSR01    .equ 0x04BD
__epsr02   .res.b 1             ;0004BE
EPSR02    .equ 0x04BE
__epsr03   .res.b 1             ;0004BF
EPSR03    .equ 0x04BF
__epsr04   .res.b 1             ;0004C0
EPSR04    .equ 0x04C0
__epsr05   .res.b 1             ;0004C1
EPSR05    .equ 0x04C1
__epsr06   .res.b 1             ;0004C2
EPSR06    .equ 0x04C2
 .org 0x0004d0
__ader0   .res.b 1             ;0004D0
ADER0    .equ 0x04D0
__ader1   .res.b 1             ;0004D1
ADER1    .equ 0x04D1
 .org 0x0004d6
__prrr0   .res.b 1             ;0004D6
PRRR0    .equ 0x04D6
__prrr1   .res.b 1             ;0004D7
PRRR1    .equ 0x04D7
__prrr2   .res.b 1             ;0004D8
PRRR2    .equ 0x04D8
__prrr3   .res.b 1             ;0004D9
PRRR3    .equ 0x04D9
__prrr4   .res.b 1             ;0004DA
PRRR4    .equ 0x04DA
__prrr5   .res.b 1             ;0004DB
PRRR5    .equ 0x04DB
__prrr6   .res.b 1             ;0004DC
PRRR6    .equ 0x04DC
__prrr7   .res.b 1             ;0004DD
PRRR7    .equ 0x04DD
__prrr8   .res.b 1             ;0004DE
PRRR8    .equ 0x04DE
__prrr9   .res.b 1             ;0004DF
PRRR9    .equ 0x04DF
__wtbr0  ; overlay symbol      ;0004E0
WTBR0    .equ 0x04E0
__wtbrl0   .res.b 1             ;0004E0
WTBRL0    .equ 0x04E0
__wtbrh0   .res.b 1             ;0004E1
WTBRH0    .equ 0x04E1
__wtbr1   .res.b 1             ;0004E2
WTBR1    .equ 0x04E2
__wtsr   .res.b 1             ;0004E3
WTSR    .equ 0x04E3
__wtmr   .res.b 1             ;0004E4
WTMR    .equ 0x04E4
__wthr   .res.b 1             ;0004E5
WTHR    .equ 0x04E5
__wtcer   .res.b 1             ;0004E6
WTCER    .equ 0x04E6
__wtcksr   .res.b 1             ;0004E7
WTCKSR    .equ 0x04E7
__wtcr  ; overlay symbol      ;0004E8
WTCR    .equ 0x04E8
__wtcrl   .res.b 1             ;0004E8
WTCRL    .equ 0x04E8
__wtcrh   .res.b 1             ;0004E9
WTCRH    .equ 0x04E9
__cucr   .res.b 1             ;0004EA
CUCR    .equ 0x04EA
 .org 0x0004ec
__cutd  ; overlay symbol      ;0004EC
CUTD    .equ 0x04EC
__cutdl   .res.b 1             ;0004EC
CUTDL    .equ 0x04EC
__cutdh   .res.b 1             ;0004ED
CUTDH    .equ 0x04ED
__cutr  ; overlay symbol      ;0004EE
CUTR    .equ 0x04EE
__cutr2  ; overlay symbol      ;0004EE
CUTR2    .equ 0x04EE
__cutr2l   .res.b 1             ;0004EE
CUTR2L    .equ 0x04EE
__cutr2h   .res.b 1             ;0004EF
CUTR2H    .equ 0x04EF
__cutr1  ; overlay symbol      ;0004F0
CUTR1    .equ 0x04F0
__cutr1l   .res.b 1             ;0004F0
CUTR1L    .equ 0x04F0
__cutr1h   .res.b 1             ;0004F1
CUTR1H    .equ 0x04F1
 .org 0x0004fa
__tmisr   .res.b 1             ;0004FA
TMISR    .equ 0x04FA
 .org 0x000500
__tcdt2   .res.b 2             ;000500
TCDT2    .equ 0x0500
__tccs2  ; overlay symbol      ;000502
TCCS2    .equ 0x0502
__tccsl2   .res.b 1             ;000502
TCCSL2    .equ 0x0502
__tccsh2   .res.b 1             ;000503
TCCSH2    .equ 0x0503
__tcdt3   .res.b 2             ;000504
TCDT3    .equ 0x0504
__tccs3  ; overlay symbol      ;000506
TCCS3    .equ 0x0506
__tccsl3   .res.b 1             ;000506
TCCSL3    .equ 0x0506
__tccsh3   .res.b 1             ;000507
TCCSH3    .equ 0x0507
 .org 0x00053e
__smr7   .res.b 1             ;00053E
SMR7    .equ 0x053E
__scr7   .res.b 1             ;00053F
SCR7    .equ 0x053F
__tdr7  ; overlay symbol      ;000540
TDR7    .equ 0x0540
__rdr7   .res.b 1             ;000540
RDR7    .equ 0x0540
__ssr7   .res.b 1             ;000541
SSR7    .equ 0x0541
__eccr7   .res.b 1             ;000542
ECCR7    .equ 0x0542
__escr7   .res.b 1             ;000543
ESCR7    .equ 0x0543
__bgr7  ; overlay symbol      ;000544
BGR7    .equ 0x0544
__bgrl7   .res.b 1             ;000544
BGRL7    .equ 0x0544
__bgrh7   .res.b 1             ;000545
BGRH7    .equ 0x0545
__esir7   .res.b 1             ;000546
ESIR7    .equ 0x0546
 .org 0x000548
__smr8   .res.b 1             ;000548
SMR8    .equ 0x0548
__scr8   .res.b 1             ;000549
SCR8    .equ 0x0549
__tdr8  ; overlay symbol      ;00054A
TDR8    .equ 0x054A
__rdr8   .res.b 1             ;00054A
RDR8    .equ 0x054A
__ssr8   .res.b 1             ;00054B
SSR8    .equ 0x054B
__eccr8   .res.b 1             ;00054C
ECCR8    .equ 0x054C
__escr8   .res.b 1             ;00054D
ESCR8    .equ 0x054D
__bgr8  ; overlay symbol      ;00054E
BGR8    .equ 0x054E
__bgrl8   .res.b 1             ;00054E
BGRL8    .equ 0x054E
__bgrh8   .res.b 1             ;00054F
BGRH8    .equ 0x054F
__esir8   .res.b 1             ;000550
ESIR8    .equ 0x0550
 .org 0x000564
__ptmr6   .res.b 2             ;000564
PTMR6    .equ 0x0564
__pcsr6   .res.b 2             ;000566
PCSR6    .equ 0x0566
__pdut6   .res.b 2             ;000568
PDUT6    .equ 0x0568
__pcn6  ; overlay symbol      ;00056A
PCN6    .equ 0x056A
__pcnl6   .res.b 1             ;00056A
PCNL6    .equ 0x056A
__pcnh6   .res.b 1             ;00056B
PCNH6    .equ 0x056B
__ptmr7   .res.b 2             ;00056C
PTMR7    .equ 0x056C
__pcsr7   .res.b 2             ;00056E
PCSR7    .equ 0x056E
__pdut7   .res.b 2             ;000570
PDUT7    .equ 0x0570
__pcn7  ; overlay symbol      ;000572
PCN7    .equ 0x0572
__pcnl7   .res.b 1             ;000572
PCNL7    .equ 0x0572
__pcnh7   .res.b 1             ;000573
PCNH7    .equ 0x0573
__gcn12  ; overlay symbol      ;000574
GCN12    .equ 0x0574
__gcn1l2   .res.b 1             ;000574
GCN1L2    .equ 0x0574
__gcn1h2   .res.b 1             ;000575
GCN1H2    .equ 0x0575
__gcn22  ; overlay symbol      ;000576
GCN22    .equ 0x0576
__gcn2l2   .res.b 1             ;000576
GCN2L2    .equ 0x0576
__gcn2h2   .res.b 1             ;000577
GCN2H2    .equ 0x0577
__ptmr8   .res.b 2             ;000578
PTMR8    .equ 0x0578
__pcsr8   .res.b 2             ;00057A
PCSR8    .equ 0x057A
__pdut8   .res.b 2             ;00057C
PDUT8    .equ 0x057C
__pcn8  ; overlay symbol      ;00057E
PCN8    .equ 0x057E
__pcnl8   .res.b 1             ;00057E
PCNL8    .equ 0x057E
__pcnh8   .res.b 1             ;00057F
PCNH8    .equ 0x057F
__ptmr9   .res.b 2             ;000580
PTMR9    .equ 0x0580
__pcsr9   .res.b 2             ;000582
PCSR9    .equ 0x0582
__pdut9   .res.b 2             ;000584
PDUT9    .equ 0x0584
__pcn9  ; overlay symbol      ;000586
PCN9    .equ 0x0586
__pcnl9   .res.b 1             ;000586
PCNL9    .equ 0x0586
__pcnh9   .res.b 1             ;000587
PCNH9    .equ 0x0587
__ptmr10   .res.b 2             ;000588
PTMR10    .equ 0x0588
__pcsr10   .res.b 2             ;00058A
PCSR10    .equ 0x058A
__pdut10   .res.b 2             ;00058C
PDUT10    .equ 0x058C
__pcn10  ; overlay symbol      ;00058E
PCN10    .equ 0x058E
__pcnl10   .res.b 1             ;00058E
PCNL10    .equ 0x058E
__pcnh10   .res.b 1             ;00058F
PCNH10    .equ 0x058F
__ptmr11   .res.b 2             ;000590
PTMR11    .equ 0x0590
__pcsr11   .res.b 2             ;000592
PCSR11    .equ 0x0592
__pdut11   .res.b 2             ;000594
PDUT11    .equ 0x0594
__pcn11  ; overlay symbol      ;000596
PCN11    .equ 0x0596
__pcnl11   .res.b 1             ;000596
PCNL11    .equ 0x0596
__pcnh11   .res.b 1             ;000597
PCNH11    .equ 0x0597
__gcn13  ; overlay symbol      ;000598
GCN13    .equ 0x0598
__gcn1l3   .res.b 1             ;000598
GCN1L3    .equ 0x0598
__gcn1h3   .res.b 1             ;000599
GCN1H3    .equ 0x0599
__gcn23  ; overlay symbol      ;00059A
GCN23    .equ 0x059A
__gcn2l3   .res.b 1             ;00059A
GCN2L3    .equ 0x059A
__gcn2h3   .res.b 1             ;00059B
GCN2H3    .equ 0x059B
__ptmr12   .res.b 2             ;00059C
PTMR12    .equ 0x059C
__pcsr12   .res.b 2             ;00059E
PCSR12    .equ 0x059E
__pdut12   .res.b 2             ;0005A0
PDUT12    .equ 0x05A0
__pcn12  ; overlay symbol      ;0005A2
PCN12    .equ 0x05A2
__pcnl12   .res.b 1             ;0005A2
PCNL12    .equ 0x05A2
__pcnh12   .res.b 1             ;0005A3
PCNH12    .equ 0x05A3
__ptmr13   .res.b 2             ;0005A4
PTMR13    .equ 0x05A4
__pcsr13   .res.b 2             ;0005A6
PCSR13    .equ 0x05A6
__pdut13   .res.b 2             ;0005A8
PDUT13    .equ 0x05A8
__pcn13  ; overlay symbol      ;0005AA
PCN13    .equ 0x05AA
__pcnl13   .res.b 1             ;0005AA
PCNL13    .equ 0x05AA
__pcnh13   .res.b 1             ;0005AB
PCNH13    .equ 0x05AB
__ptmr14   .res.b 2             ;0005AC
PTMR14    .equ 0x05AC
__pcsr14   .res.b 2             ;0005AE
PCSR14    .equ 0x05AE
__pdut14   .res.b 2             ;0005B0
PDUT14    .equ 0x05B0
__pcn14  ; overlay symbol      ;0005B2
PCN14    .equ 0x05B2
__pcnl14   .res.b 1             ;0005B2
PCNL14    .equ 0x05B2
__pcnh14   .res.b 1             ;0005B3
PCNH14    .equ 0x05B3
__ptmr15   .res.b 2             ;0005B4
PTMR15    .equ 0x05B4
__pcsr15   .res.b 2             ;0005B6
PCSR15    .equ 0x05B6
__pdut15   .res.b 2             ;0005B8
PDUT15    .equ 0x05B8
__pcn15  ; overlay symbol      ;0005BA
PCN15    .equ 0x05BA
__pcnl15   .res.b 1             ;0005BA
PCNL15    .equ 0x05BA
__pcnh15   .res.b 1             ;0005BB
PCNH15    .equ 0x05BB
__gcn14  ; overlay symbol      ;0005BC
GCN14    .equ 0x05BC
__gcn1l4   .res.b 1             ;0005BC
GCN1L4    .equ 0x05BC
__gcn1h4   .res.b 1             ;0005BD
GCN1H4    .equ 0x05BD
__gcn24  ; overlay symbol      ;0005BE
GCN24    .equ 0x05BE
__gcn2l4   .res.b 1             ;0005BE
GCN2L4    .equ 0x05BE
__gcn2h4   .res.b 1             ;0005BF
GCN2H4    .equ 0x05BF
__ptmr16   .res.b 2             ;0005C0
PTMR16    .equ 0x05C0
__pcsr16   .res.b 2             ;0005C2
PCSR16    .equ 0x05C2
__pdut16   .res.b 2             ;0005C4
PDUT16    .equ 0x05C4
__pcn16  ; overlay symbol      ;0005C6
PCN16    .equ 0x05C6
__pcnl16   .res.b 1             ;0005C6
PCNL16    .equ 0x05C6
__pcnh16   .res.b 1             ;0005C7
PCNH16    .equ 0x05C7
__ptmr17   .res.b 2             ;0005C8
PTMR17    .equ 0x05C8
__pcsr17   .res.b 2             ;0005CA
PCSR17    .equ 0x05CA
__pdut17   .res.b 2             ;0005CC
PDUT17    .equ 0x05CC
__pcn17  ; overlay symbol      ;0005CE
PCN17    .equ 0x05CE
__pcnl17   .res.b 1             ;0005CE
PCNL17    .equ 0x05CE
__pcnh17   .res.b 1             ;0005CF
PCNH17    .equ 0x05CF
__ptmr18   .res.b 2             ;0005D0
PTMR18    .equ 0x05D0
__pcsr18   .res.b 2             ;0005D2
PCSR18    .equ 0x05D2
__pdut18   .res.b 2             ;0005D4
PDUT18    .equ 0x05D4
__pcn18  ; overlay symbol      ;0005D6
PCN18    .equ 0x05D6
__pcnl18   .res.b 1             ;0005D6
PCNL18    .equ 0x05D6
__pcnh18   .res.b 1             ;0005D7
PCNH18    .equ 0x05D7
__ptmr19   .res.b 2             ;0005D8
PTMR19    .equ 0x05D8
__pcsr19   .res.b 2             ;0005DA
PCSR19    .equ 0x05DA
__pdut19   .res.b 2             ;0005DC
PDUT19    .equ 0x05DC
__pcn19  ; overlay symbol      ;0005DE
PCN19    .equ 0x05DE
__pcnl19   .res.b 1             ;0005DE
PCNL19    .equ 0x05DE
__pcnh19   .res.b 1             ;0005DF
PCNH19    .equ 0x05DF
 .org 0x000660
__prrr10   .res.b 1             ;000660
PRRR10    .equ 0x0660
__prrr11   .res.b 1             ;000661
PRRR11    .equ 0x0661
__prrr12   .res.b 1             ;000662
PRRR12    .equ 0x0662
__prrr13   .res.b 1             ;000663
PRRR13    .equ 0x0663
 .org 0x0006e0
__eac0  ; overlay symbol      ;0006E0
EAC0    .equ 0x06E0
__eacl0   .res.b 1             ;0006E0
EACL0    .equ 0x06E0
__each0   .res.b 1             ;0006E1
EACH0    .equ 0x06E1
__eac1  ; overlay symbol      ;0006E2
EAC1    .equ 0x06E2
__eacl1   .res.b 1             ;0006E2
EACL1    .equ 0x06E2
__each1   .res.b 1             ;0006E3
EACH1    .equ 0x06E3
__eac2  ; overlay symbol      ;0006E4
EAC2    .equ 0x06E4
__eacl2   .res.b 1             ;0006E4
EACL2    .equ 0x06E4
__each2   .res.b 1             ;0006E5
EACH2    .equ 0x06E5
__eac3  ; overlay symbol      ;0006E6
EAC3    .equ 0x06E6
__eacl3   .res.b 1             ;0006E6
EACL3    .equ 0x06E6
__each3   .res.b 1             ;0006E7
EACH3    .equ 0x06E7
__eac4  ; overlay symbol      ;0006E8
EAC4    .equ 0x06E8
__eacl4   .res.b 1             ;0006E8
EACL4    .equ 0x06E8
__each4   .res.b 1             ;0006E9
EACH4    .equ 0x06E9
__eac5  ; overlay symbol      ;0006EA
EAC5    .equ 0x06EA
__eacl5   .res.b 1             ;0006EA
EACL5    .equ 0x06EA
__each5   .res.b 1             ;0006EB
EACH5    .equ 0x06EB
__eas2   .res.b 1             ;0006EC
EAS2    .equ 0x06EC
__eas3   .res.b 1             ;0006ED
EAS3    .equ 0x06ED
__eas4   .res.b 1             ;0006EE
EAS4    .equ 0x06EE
__eas5   .res.b 1             ;0006EF
EAS5    .equ 0x06EF
__ebm   .res.b 1             ;0006F0
EBM    .equ 0x06F0
__ebcf   .res.b 1             ;0006F1
EBCF    .equ 0x06F1
__ebae0   .res.b 1             ;0006F2
EBAE0    .equ 0x06F2
__ebae1   .res.b 1             ;0006F3
EBAE1    .equ 0x06F3
__ebae2   .res.b 1             ;0006F4
EBAE2    .equ 0x06F4
__ebcs   .res.b 1             ;0006F5
EBCS    .equ 0x06F5
 .org 0x000800
__ctrlr1  ; overlay symbol      ;000800
CTRLR1    .equ 0x0800
__ctrlrl1   .res.b 1             ;000800
CTRLRL1    .equ 0x0800
__ctrlrh1   .res.b 1             ;000801
CTRLRH1    .equ 0x0801
__statr1  ; overlay symbol      ;000802
STATR1    .equ 0x0802
__statrl1   .res.b 1             ;000802
STATRL1    .equ 0x0802
__statrh1   .res.b 1             ;000803
STATRH1    .equ 0x0803
__errcnt1  ; overlay symbol      ;000804
ERRCNT1    .equ 0x0804
__errcntl1   .res.b 1             ;000804
ERRCNTL1    .equ 0x0804
__errcnth1   .res.b 1             ;000805
ERRCNTH1    .equ 0x0805
__btr1  ; overlay symbol      ;000806
BTR1    .equ 0x0806
__btrl1   .res.b 1             ;000806
BTRL1    .equ 0x0806
__btrh1   .res.b 1             ;000807
BTRH1    .equ 0x0807
__intr1  ; overlay symbol      ;000808
INTR1    .equ 0x0808
__intrl1   .res.b 1             ;000808
INTRL1    .equ 0x0808
__intrh1   .res.b 1             ;000809
INTRH1    .equ 0x0809
__testr1  ; overlay symbol      ;00080A
TESTR1    .equ 0x080A
__testrl1   .res.b 1             ;00080A
TESTRL1    .equ 0x080A
__testrh1   .res.b 1             ;00080B
TESTRH1    .equ 0x080B
__brper1  ; overlay symbol      ;00080C
BRPER1    .equ 0x080C
__brperl1   .res.b 1             ;00080C
BRPERL1    .equ 0x080C
__brperh1   .res.b 1             ;00080D
BRPERH1    .equ 0x080D
 .org 0x000810
__if1creq1  ; overlay symbol      ;000810
IF1CREQ1    .equ 0x0810
__if1creql1   .res.b 1             ;000810
IF1CREQL1    .equ 0x0810
__if1creqh1   .res.b 1             ;000811
IF1CREQH1    .equ 0x0811
__if1cmsk1  ; overlay symbol      ;000812
IF1CMSK1    .equ 0x0812
__if1cmskl1   .res.b 1             ;000812
IF1CMSKL1    .equ 0x0812
__if1cmskh1   .res.b 1             ;000813
IF1CMSKH1    .equ 0x0813
__if1msk1  ; overlay symbol      ;000814
IF1MSK1    .equ 0x0814
__if1msk11  ; overlay symbol      ;000814
IF1MSK11    .equ 0x0814
__if1msk1l1   .res.b 1             ;000814
IF1MSK1L1    .equ 0x0814
__if1msk1h1   .res.b 1             ;000815
IF1MSK1H1    .equ 0x0815
__if1msk21  ; overlay symbol      ;000816
IF1MSK21    .equ 0x0816
__if1msk2l1   .res.b 1             ;000816
IF1MSK2L1    .equ 0x0816
__if1msk2h1   .res.b 1             ;000817
IF1MSK2H1    .equ 0x0817
__if1arb1  ; overlay symbol      ;000818
IF1ARB1    .equ 0x0818
__if1arb11  ; overlay symbol      ;000818
IF1ARB11    .equ 0x0818
__if1arb1l1   .res.b 1             ;000818
IF1ARB1L1    .equ 0x0818
__if1arb1h1   .res.b 1             ;000819
IF1ARB1H1    .equ 0x0819
__if1arb21  ; overlay symbol      ;00081A
IF1ARB21    .equ 0x081A
__if1arb2l1   .res.b 1             ;00081A
IF1ARB2L1    .equ 0x081A
__if1arb2h1   .res.b 1             ;00081B
IF1ARB2H1    .equ 0x081B
__if1mctr1  ; overlay symbol      ;00081C
IF1MCTR1    .equ 0x081C
__if1mctrl1   .res.b 1             ;00081C
IF1MCTRL1    .equ 0x081C
__if1mctrh1   .res.b 1             ;00081D
IF1MCTRH1    .equ 0x081D
__if1dta1  ; overlay symbol      ;00081E
IF1DTA1    .equ 0x081E
__if1dta11  ; overlay symbol      ;00081E
IF1DTA11    .equ 0x081E
__if1dta1l1   .res.b 1             ;00081E
IF1DTA1L1    .equ 0x081E
__if1dta1h1   .res.b 1             ;00081F
IF1DTA1H1    .equ 0x081F
__if1dta21  ; overlay symbol      ;000820
IF1DTA21    .equ 0x0820
__if1dta2l1   .res.b 1             ;000820
IF1DTA2L1    .equ 0x0820
__if1dta2h1   .res.b 1             ;000821
IF1DTA2H1    .equ 0x0821
__if1dtb1  ; overlay symbol      ;000822
IF1DTB1    .equ 0x0822
__if1dtb11  ; overlay symbol      ;000822
IF1DTB11    .equ 0x0822
__if1dtb1l1   .res.b 1             ;000822
IF1DTB1L1    .equ 0x0822
__if1dtb1h1   .res.b 1             ;000823
IF1DTB1H1    .equ 0x0823
__if1dtb21  ; overlay symbol      ;000824
IF1DTB21    .equ 0x0824
__if1dtb2l1   .res.b 1             ;000824
IF1DTB2L1    .equ 0x0824
__if1dtb2h1   .res.b 1             ;000825
IF1DTB2H1    .equ 0x0825
 .org 0x000840
__if2creq1  ; overlay symbol      ;000840
IF2CREQ1    .equ 0x0840
__if2creql1   .res.b 1             ;000840
IF2CREQL1    .equ 0x0840
__if2creqh1   .res.b 1             ;000841
IF2CREQH1    .equ 0x0841
__if2cmsk1  ; overlay symbol      ;000842
IF2CMSK1    .equ 0x0842
__if2cmskl1   .res.b 1             ;000842
IF2CMSKL1    .equ 0x0842
__if2cmskh1   .res.b 1             ;000843
IF2CMSKH1    .equ 0x0843
__if2msk1  ; overlay symbol      ;000844
IF2MSK1    .equ 0x0844
__if2msk11  ; overlay symbol      ;000844
IF2MSK11    .equ 0x0844
__if2msk1l1   .res.b 1             ;000844
IF2MSK1L1    .equ 0x0844
__if2msk1h1   .res.b 1             ;000845
IF2MSK1H1    .equ 0x0845
__if2msk21  ; overlay symbol      ;000846
IF2MSK21    .equ 0x0846
__if2msk2l1   .res.b 1             ;000846
IF2MSK2L1    .equ 0x0846
__if2msk2h1   .res.b 1             ;000847
IF2MSK2H1    .equ 0x0847
__if2arb1  ; overlay symbol      ;000848
IF2ARB1    .equ 0x0848
__if2arb11  ; overlay symbol      ;000848
IF2ARB11    .equ 0x0848
__if2arb1l1   .res.b 1             ;000848
IF2ARB1L1    .equ 0x0848
__if2arb1h1   .res.b 1             ;000849
IF2ARB1H1    .equ 0x0849
__if2arb21  ; overlay symbol      ;00084A
IF2ARB21    .equ 0x084A
__if2arb2l1   .res.b 1             ;00084A
IF2ARB2L1    .equ 0x084A
__if2arb2h1   .res.b 1             ;00084B
IF2ARB2H1    .equ 0x084B
__if2mctr1  ; overlay symbol      ;00084C
IF2MCTR1    .equ 0x084C
__if2mctrl1   .res.b 1             ;00084C
IF2MCTRL1    .equ 0x084C
__if2mctrh1   .res.b 1             ;00084D
IF2MCTRH1    .equ 0x084D
__if2dta1  ; overlay symbol      ;00084E
IF2DTA1    .equ 0x084E
__if2dta11  ; overlay symbol      ;00084E
IF2DTA11    .equ 0x084E
__if2dta1l1   .res.b 1             ;00084E
IF2DTA1L1    .equ 0x084E
__if2dta1h1   .res.b 1             ;00084F
IF2DTA1H1    .equ 0x084F
__if2dta21  ; overlay symbol      ;000850
IF2DTA21    .equ 0x0850
__if2dta2l1   .res.b 1             ;000850
IF2DTA2L1    .equ 0x0850
__if2dta2h1   .res.b 1             ;000851
IF2DTA2H1    .equ 0x0851
__if2dtb1  ; overlay symbol      ;000852
IF2DTB1    .equ 0x0852
__if2dtb11  ; overlay symbol      ;000852
IF2DTB11    .equ 0x0852
__if2dtb1l1   .res.b 1             ;000852
IF2DTB1L1    .equ 0x0852
__if2dtb1h1   .res.b 1             ;000853
IF2DTB1H1    .equ 0x0853
__if2dtb21  ; overlay symbol      ;000854
IF2DTB21    .equ 0x0854
__if2dtb2l1   .res.b 1             ;000854
IF2DTB2L1    .equ 0x0854
__if2dtb2h1   .res.b 1             ;000855
IF2DTB2H1    .equ 0x0855
 .org 0x000880
__treqr1  ; overlay symbol      ;000880
TREQR1    .equ 0x0880
__treqr11  ; overlay symbol      ;000880
TREQR11    .equ 0x0880
__treqr1l1   .res.b 1             ;000880
TREQR1L1    .equ 0x0880
__treqr1h1   .res.b 1             ;000881
TREQR1H1    .equ 0x0881
__treqr21  ; overlay symbol      ;000882
TREQR21    .equ 0x0882
__treqr2l1   .res.b 1             ;000882
TREQR2L1    .equ 0x0882
__treqr2h1   .res.b 1             ;000883
TREQR2H1    .equ 0x0883
 .org 0x000890
__newdt1  ; overlay symbol      ;000890
NEWDT1    .equ 0x0890
__newdt11  ; overlay symbol      ;000890
NEWDT11    .equ 0x0890
__newdt1l1   .res.b 1             ;000890
NEWDT1L1    .equ 0x0890
__newdt1h1   .res.b 1             ;000891
NEWDT1H1    .equ 0x0891
__newdt21  ; overlay symbol      ;000892
NEWDT21    .equ 0x0892
__newdt2l1   .res.b 1             ;000892
NEWDT2L1    .equ 0x0892
__newdt2h1   .res.b 1             ;000893
NEWDT2H1    .equ 0x0893
 .org 0x0008A0
__intpnd1  ; overlay symbol      ;0008A0
INTPND1    .equ 0x08A0
__intpnd11  ; overlay symbol      ;0008A0
INTPND11    .equ 0x08A0
__intpnd1l1   .res.b 1             ;0008A0
INTPND1L1    .equ 0x08A0
__intpnd1h1   .res.b 1             ;0008A1
INTPND1H1    .equ 0x08A1
__intpnd21  ; overlay symbol      ;0008A2
INTPND21    .equ 0x08A2
__intpnd2l1   .res.b 1             ;0008A2
INTPND2L1    .equ 0x08A2
__intpnd2h1   .res.b 1             ;0008A3
INTPND2H1    .equ 0x08A3
 .org 0x0008B0
__msgval1  ; overlay symbol      ;0008B0
MSGVAL1    .equ 0x08B0
__msgval11  ; overlay symbol      ;0008B0
MSGVAL11    .equ 0x08B0
__msgval1l1   .res.b 1             ;0008B0
MSGVAL1L1    .equ 0x08B0
__msgval1h1   .res.b 1             ;0008B1
MSGVAL1H1    .equ 0x08B1
__msgval21  ; overlay symbol      ;0008B2
MSGVAL21    .equ 0x08B2
__msgval2l1   .res.b 1             ;0008B2
MSGVAL2L1    .equ 0x08B2
__msgval2h1   .res.b 1             ;0008B3
MSGVAL2H1    .equ 0x08B3
 .org 0x0008CE
__coer1   .res.b 1             ;0008CE
COER1    .equ 0x08CE
 .org 0x000900
__ctrlr2  ; overlay symbol      ;000900
CTRLR2    .equ 0x0900
__ctrlrl2   .res.b 1             ;000900
CTRLRL2    .equ 0x0900
__ctrlrh2   .res.b 1             ;000901
CTRLRH2    .equ 0x0901
__statr2  ; overlay symbol      ;000902
STATR2    .equ 0x0902
__statrl2   .res.b 1             ;000902
STATRL2    .equ 0x0902
__statrh2   .res.b 1             ;000903
STATRH2    .equ 0x0903
__errcnt2  ; overlay symbol      ;000904
ERRCNT2    .equ 0x0904
__errcntl2   .res.b 1             ;000904
ERRCNTL2    .equ 0x0904
__errcnth2   .res.b 1             ;000905
ERRCNTH2    .equ 0x0905
__btr2  ; overlay symbol      ;000906
BTR2    .equ 0x0906
__btrl2   .res.b 1             ;000906
BTRL2    .equ 0x0906
__btrh2   .res.b 1             ;000907
BTRH2    .equ 0x0907
__intr2  ; overlay symbol      ;000908
INTR2    .equ 0x0908
__intrl2   .res.b 1             ;000908
INTRL2    .equ 0x0908
__intrh2   .res.b 1             ;000909
INTRH2    .equ 0x0909
__testr2  ; overlay symbol      ;00090A
TESTR2    .equ 0x090A
__testrl2   .res.b 1             ;00090A
TESTRL2    .equ 0x090A
__testrh2   .res.b 1             ;00090B
TESTRH2    .equ 0x090B
__brper2  ; overlay symbol      ;00090C
BRPER2    .equ 0x090C
__brperl2   .res.b 1             ;00090C
BRPERL2    .equ 0x090C
__brperh2   .res.b 1             ;00090D
BRPERH2    .equ 0x090D
 .org 0x000910
__if1creq2  ; overlay symbol      ;000910
IF1CREQ2    .equ 0x0910
__if1creql2   .res.b 1             ;000910
IF1CREQL2    .equ 0x0910
__if1creqh2   .res.b 1             ;000911
IF1CREQH2    .equ 0x0911
__if1cmsk2  ; overlay symbol      ;000912
IF1CMSK2    .equ 0x0912
__if1cmskl2   .res.b 1             ;000912
IF1CMSKL2    .equ 0x0912
__if1cmskh2   .res.b 1             ;000913
IF1CMSKH2    .equ 0x0913
__if1msk2  ; overlay symbol      ;000914
IF1MSK2    .equ 0x0914
__if1msk12  ; overlay symbol      ;000914
IF1MSK12    .equ 0x0914
__if1msk1l2   .res.b 1             ;000914
IF1MSK1L2    .equ 0x0914
__if1msk1h2   .res.b 1             ;000915
IF1MSK1H2    .equ 0x0915
__if1msk22  ; overlay symbol      ;000916
IF1MSK22    .equ 0x0916
__if1msk2l2   .res.b 1             ;000916
IF1MSK2L2    .equ 0x0916
__if1msk2h2   .res.b 1             ;000917
IF1MSK2H2    .equ 0x0917
__if1arb2  ; overlay symbol      ;000918
IF1ARB2    .equ 0x0918
__if1arb12  ; overlay symbol      ;000918
IF1ARB12    .equ 0x0918
__if1arb1l2   .res.b 1             ;000918
IF1ARB1L2    .equ 0x0918
__if1arb1h2   .res.b 1             ;000919
IF1ARB1H2    .equ 0x0919
__if1arb22  ; overlay symbol      ;00091A
IF1ARB22    .equ 0x091A
__if1arb2l2   .res.b 1             ;00091A
IF1ARB2L2    .equ 0x091A
__if1arb2h2   .res.b 1             ;00091B
IF1ARB2H2    .equ 0x091B
__if1mctr2  ; overlay symbol      ;00091C
IF1MCTR2    .equ 0x091C
__if1mctrl2   .res.b 1             ;00091C
IF1MCTRL2    .equ 0x091C
__if1mctrh2   .res.b 1             ;00091D
IF1MCTRH2    .equ 0x091D
__if1dta2  ; overlay symbol      ;00091E
IF1DTA2    .equ 0x091E
__if1dta12  ; overlay symbol      ;00091E
IF1DTA12    .equ 0x091E
__if1dta1l2   .res.b 1             ;00091E
IF1DTA1L2    .equ 0x091E
__if1dta1h2   .res.b 1             ;00091F
IF1DTA1H2    .equ 0x091F
__if1dta22  ; overlay symbol      ;000920
IF1DTA22    .equ 0x0920
__if1dta2l2   .res.b 1             ;000920
IF1DTA2L2    .equ 0x0920
__if1dta2h2   .res.b 1             ;000921
IF1DTA2H2    .equ 0x0921
__if1dtb2  ; overlay symbol      ;000922
IF1DTB2    .equ 0x0922
__if1dtb12  ; overlay symbol      ;000922
IF1DTB12    .equ 0x0922
__if1dtb1l2   .res.b 1             ;000922
IF1DTB1L2    .equ 0x0922
__if1dtb1h2   .res.b 1             ;000923
IF1DTB1H2    .equ 0x0923
__if1dtb22  ; overlay symbol      ;000924
IF1DTB22    .equ 0x0924
__if1dtb2l2   .res.b 1             ;000924
IF1DTB2L2    .equ 0x0924
__if1dtb2h2   .res.b 1             ;000925
IF1DTB2H2    .equ 0x0925
 .org 0x000940
__if2creq2  ; overlay symbol      ;000940
IF2CREQ2    .equ 0x0940
__if2creql2   .res.b 1             ;000940
IF2CREQL2    .equ 0x0940
__if2creqh2   .res.b 1             ;000941
IF2CREQH2    .equ 0x0941
__if2cmsk2  ; overlay symbol      ;000942
IF2CMSK2    .equ 0x0942
__if2cmskl2   .res.b 1             ;000942
IF2CMSKL2    .equ 0x0942
__if2cmskh2   .res.b 1             ;000943
IF2CMSKH2    .equ 0x0943
__if2msk2  ; overlay symbol      ;000944
IF2MSK2    .equ 0x0944
__if2msk12  ; overlay symbol      ;000944
IF2MSK12    .equ 0x0944
__if2msk1l2   .res.b 1             ;000944
IF2MSK1L2    .equ 0x0944
__if2msk1h2   .res.b 1             ;000945
IF2MSK1H2    .equ 0x0945
__if2msk22  ; overlay symbol      ;000946
IF2MSK22    .equ 0x0946
__if2msk2l2   .res.b 1             ;000946
IF2MSK2L2    .equ 0x0946
__if2msk2h2   .res.b 1             ;000947
IF2MSK2H2    .equ 0x0947
__if2arb2  ; overlay symbol      ;000948
IF2ARB2    .equ 0x0948
__if2arb12  ; overlay symbol      ;000948
IF2ARB12    .equ 0x0948
__if2arb1l2   .res.b 1             ;000948
IF2ARB1L2    .equ 0x0948
__if2arb1h2   .res.b 1             ;000949
IF2ARB1H2    .equ 0x0949
__if2arb22  ; overlay symbol      ;00094A
IF2ARB22    .equ 0x094A
__if2arb2l2   .res.b 1             ;00094A
IF2ARB2L2    .equ 0x094A
__if2arb2h2   .res.b 1             ;00094B
IF2ARB2H2    .equ 0x094B
__if2mctr2  ; overlay symbol      ;00094C
IF2MCTR2    .equ 0x094C
__if2mctrl2   .res.b 1             ;00094C
IF2MCTRL2    .equ 0x094C
__if2mctrh2   .res.b 1             ;00094D
IF2MCTRH2    .equ 0x094D
__if2dta2  ; overlay symbol      ;00094E
IF2DTA2    .equ 0x094E
__if2dta12  ; overlay symbol      ;00094E
IF2DTA12    .equ 0x094E
__if2dta1l2   .res.b 1             ;00094E
IF2DTA1L2    .equ 0x094E
__if2dta1h2   .res.b 1             ;00094F
IF2DTA1H2    .equ 0x094F
__if2dta22  ; overlay symbol      ;000950
IF2DTA22    .equ 0x0950
__if2dta2l2   .res.b 1             ;000950
IF2DTA2L2    .equ 0x0950
__if2dta2h2   .res.b 1             ;000951
IF2DTA2H2    .equ 0x0951
__if2dtb2  ; overlay symbol      ;000952
IF2DTB2    .equ 0x0952
__if2dtb12  ; overlay symbol      ;000952
IF2DTB12    .equ 0x0952
__if2dtb1l2   .res.b 1             ;000952
IF2DTB1L2    .equ 0x0952
__if2dtb1h2   .res.b 1             ;000953
IF2DTB1H2    .equ 0x0953
__if2dtb22  ; overlay symbol      ;000954
IF2DTB22    .equ 0x0954
__if2dtb2l2   .res.b 1             ;000954
IF2DTB2L2    .equ 0x0954
__if2dtb2h2   .res.b 1             ;000955
IF2DTB2H2    .equ 0x0955
 .org 0x000980
__treqr2  ; overlay symbol      ;000980
TREQR2    .equ 0x0980
__treqr12  ; overlay symbol      ;000980
TREQR12    .equ 0x0980
__treqr1l2   .res.b 1             ;000980
TREQR1L2    .equ 0x0980
__treqr1h2   .res.b 1             ;000981
TREQR1H2    .equ 0x0981
__treqr22  ; overlay symbol      ;000982
TREQR22    .equ 0x0982
__treqr2l2   .res.b 1             ;000982
TREQR2L2    .equ 0x0982
__treqr2h2   .res.b 1             ;000983
TREQR2H2    .equ 0x0983
 .org 0x000990
__newdt2  ; overlay symbol      ;000990
NEWDT2    .equ 0x0990
__newdt12  ; overlay symbol      ;000990
NEWDT12    .equ 0x0990
__newdt1l2   .res.b 1             ;000990
NEWDT1L2    .equ 0x0990
__newdt1h2   .res.b 1             ;000991
NEWDT1H2    .equ 0x0991
__newdt22  ; overlay symbol      ;000992
NEWDT22    .equ 0x0992
__newdt2l2   .res.b 1             ;000992
NEWDT2L2    .equ 0x0992
__newdt2h2   .res.b 1             ;000993
NEWDT2H2    .equ 0x0993
 .org 0x0009A0
__intpnd2  ; overlay symbol      ;0009A0
INTPND2    .equ 0x09A0
__intpnd12  ; overlay symbol      ;0009A0
INTPND12    .equ 0x09A0
__intpnd1l2   .res.b 1             ;0009A0
INTPND1L2    .equ 0x09A0
__intpnd1h2   .res.b 1             ;0009A1
INTPND1H2    .equ 0x09A1
__intpnd22  ; overlay symbol      ;0009A2
INTPND22    .equ 0x09A2
__intpnd2l2   .res.b 1             ;0009A2
INTPND2L2    .equ 0x09A2
__intpnd2h2   .res.b 1             ;0009A3
INTPND2H2    .equ 0x09A3
 .org 0x0009B0
__msgval2  ; overlay symbol      ;0009B0
MSGVAL2    .equ 0x09B0
__msgval12  ; overlay symbol      ;0009B0
MSGVAL12    .equ 0x09B0
__msgval1l2   .res.b 1             ;0009B0
MSGVAL1L2    .equ 0x09B0
__msgval1h2   .res.b 1             ;0009B1
MSGVAL1H2    .equ 0x09B1
__msgval22  ; overlay symbol      ;0009B2
MSGVAL22    .equ 0x09B2
__msgval2l2   .res.b 1             ;0009B2
MSGVAL2L2    .equ 0x09B2
__msgval2h2   .res.b 1             ;0009B3
MSGVAL2H2    .equ 0x09B3
 .org 0x0009CE
__coer2   .res.b 1             ;0009CE
COER2    .equ 0x09CE


 .end
