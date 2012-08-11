/* FFMC-16 IO-MAP HEADER FILE                                                */
/* ==========================                                                */
/* SOFTUNE WORKBENCH FORMAT                                                  */
/* C-DEFINITIONS FOR IO-SYMBOLS                                              */
/* CREATED BY IO-WIZARD V2.27                                                */
/* $Id: mb96348hs.h,v 1.7 2007/09/20 14:23:33 mwilla Exp $ */
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
/* This header-file covers all features of the chip MB96F348HS.              */
/*                                                                           */
/*                                                                           */
/* ----------------------------------------------------------------------    */
/* History:                                                                  */
/* Date        Version  Author  Description                                  */
/* 22.12.2006   1.0     PHu     Initial Release: derived from headerfile of  */
/*                              MB96348RS and added Satellite Flash, removed */
/*                              RTC, Clock Calibration, LIN-USART7-9         */
/* 16.01.2007   1.1     PHu     Add 32-bit access names for CAN where        */
/*                              appropriate                                  */
/* 09.02.2007   1.3     PHu     skip version 1.2 to be in line with CVS      */
/*                              numbering                                    */
/*                              correct addresses of LIN-UART3 registers     */
/*                              allow only 16 bit access for the ADSR        */
/* 12.04.2007   1.4     Mef     Added Voltage Regulator Control Register     */
/*                              Added RD19V bit in Flash Memory Control      */
/*                              Status Register                              */
/* 03.05.2007   1.5     Mef     Added LIN USART 7,8,9                        */
/* 15.05.2007   1.6     Mef     Added RTC                                    */
/* 20.09.2007   1.7     MWi     Completely revised version                   */


#ifndef   __MB96XXX_H
#  define __MB96XXX_H
/*
- Please define __IO_NEAR in LARGE and COMPACT memory model, if the default
  data bank (DTB) is 00. This will result in better performance in these
  models.
- Please define __IO_FAR in SMALL and MEDIUM memory model, if the default
  data bank (DTB) is other than 00. This might be the case in systems with
  external RAM, which are not using internal RAM as default data area.
- Please define neither __IO_NEAR nor __IO_FAR in all other cases. This
  will work with almost all configurations.
*/

#  ifdef  __IO_NEAR
#    ifdef  __IO_FAR
#      error __IO_NEAR and __IO_FAR must not be defined at the same time
#    else
#      define ___IOWIDTH __near
#    endif
#  else
#    ifdef __IO_FAR
#      define ___IOWIDTH __far
#    else                               /* specified by memory model */
#      define ___IOWIDTH
#    endif
#  endif
#  ifdef  __IO_DEFINE
#    define __IO_EXTERN
#    define __IO_EXTENDED volatile ___IOWIDTH
#  else
#    define __IO_EXTERN   extern      /* for data, which can have __io */
#    define __IO_EXTENDED extern volatile ___IOWIDTH
#  endif

typedef unsigned char		IO_BYTE;
typedef unsigned short		IO_WORD;
typedef unsigned long		IO_LWORD;
typedef const unsigned short	IO_WORD_READ;

/* REGISTER BIT STRUCTURES */

typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _P0 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P3 :1;
    IO_BYTE _P4 :1;
    IO_BYTE _P5 :1;
    IO_BYTE _P6 :1;
    IO_BYTE _P7 :1;
  }bit;
 }PDR00STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _P0 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P3 :1;
    IO_BYTE _P4 :1;
    IO_BYTE _P5 :1;
    IO_BYTE _P6 :1;
    IO_BYTE _P7 :1;
  }bit;
 }PDR01STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _P0 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P3 :1;
    IO_BYTE _P4 :1;
    IO_BYTE _P5 :1;
    IO_BYTE _P6 :1;
    IO_BYTE _P7 :1;
  }bit;
 }PDR02STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _P0 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P3 :1;
    IO_BYTE _P4 :1;
    IO_BYTE _P5 :1;
    IO_BYTE _P6 :1;
    IO_BYTE _P7 :1;
  }bit;
 }PDR03STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _P0 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P3 :1;
    IO_BYTE _P4 :1;
    IO_BYTE _P5 :1;
    IO_BYTE _P6 :1;
    IO_BYTE _P7 :1;
  }bit;
 }PDR04STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _P0 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P3 :1;
    IO_BYTE _P4 :1;
    IO_BYTE _P5 :1;
    IO_BYTE _P6 :1;
    IO_BYTE _P7 :1;
  }bit;
 }PDR05STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _P0 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P3 :1;
    IO_BYTE _P4 :1;
    IO_BYTE _P5 :1;
    IO_BYTE _P6 :1;
    IO_BYTE _P7 :1;
  }bit;
 }PDR06STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _P0 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P3 :1;
    IO_BYTE _P4 :1;
    IO_BYTE _P5 :1;
    IO_BYTE _P6 :1;
    IO_BYTE _P7 :1;
  }bit;
 }PDR07STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _P0 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P3 :1;
    IO_BYTE _P4 :1;
    IO_BYTE _P5 :1;
    IO_BYTE _P6 :1;
    IO_BYTE _P7 :1;
  }bit;
 }PDR08STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _P0 :1;
    IO_BYTE _P1 :1;
    IO_BYTE _P2 :1;
    IO_BYTE _P3 :1;
    IO_BYTE _P4 :1;
    IO_BYTE _P5 :1;
    IO_BYTE _P6 :1;
    IO_BYTE _P7 :1;
  }bit;
 }PDR09STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _P0 :1;
    IO_BYTE _P1 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }PDR10STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _resv :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _S10 :1;
    IO_WORD _MD0 :1;
    IO_WORD _MD1 :1;
    IO_WORD  :1;
    IO_WORD _STRT :1;
    IO_WORD _STS0 :1;
    IO_WORD _STS1 :1;
    IO_WORD _PAUS :1;
    IO_WORD _INTE :1;
    IO_WORD _INT :1;
    IO_WORD _BUSY :1;
  }bit;
  struct{
    IO_WORD :6;
    IO_WORD _MD :2;
    IO_WORD :2;
    IO_WORD _STS :2;
  }bitc;
 }ADCSSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _resv :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _S10 :1;
    IO_BYTE _MD0 :1;
    IO_BYTE _MD1 :1;
  }bit;
  struct{
    IO_BYTE :6;
    IO_BYTE _MD :2;
  }bitc;
 }ADCSLSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE _STRT :1;
    IO_BYTE _STS0 :1;
    IO_BYTE _STS1 :1;
    IO_BYTE _PAUS :1;
    IO_BYTE _INTE :1;
    IO_BYTE _INT :1;
    IO_BYTE _BUSY :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _STS :2;
  }bitc;
 }ADCSHSTR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD _D :10;
  }bitc;
 }ADCRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _D0 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D7 :1;
  }bit;
 }ADCRLSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _D8 :1;
    IO_BYTE _D9 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }ADCRHSTR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _ANE0 :1;
    IO_WORD _ANE1 :1;
    IO_WORD _ANE2 :1;
    IO_WORD _ANE3 :1;
    IO_WORD _ANE4 :1;
    IO_WORD _ANS0 :1;
    IO_WORD _ANS1 :1;
    IO_WORD _ANS2 :1;
    IO_WORD _ANS3 :1;
    IO_WORD _ANS4 :1;
    IO_WORD _CT0 :1;
    IO_WORD _CT1 :1;
    IO_WORD _CT2 :1;
    IO_WORD _ST0 :1;
    IO_WORD _ST1 :1;
    IO_WORD _ST2 :1;
  }bit;
 }ADSRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ADSEL :1;
    IO_BYTE _HSEL :1;
    IO_BYTE _LSEL :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }ADECRSTR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _T0 :1;
    IO_WORD _T1 :1;
    IO_WORD _T2 :1;
    IO_WORD _T3 :1;
    IO_WORD _T4 :1;
    IO_WORD _T5 :1;
    IO_WORD _T6 :1;
    IO_WORD _T7 :1;
    IO_WORD _T8 :1;
    IO_WORD _T9 :1;
    IO_WORD _T10 :1;
    IO_WORD _T11 :1;
    IO_WORD _T12 :1;
    IO_WORD _T13 :1;
    IO_WORD _T14 :1;
    IO_WORD _T15 :1;
  }bit;
  struct{
    IO_WORD _T :16;
  }bitc;
 }TCDT0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _CLK0 :1;
    IO_WORD _CLK1 :1;
    IO_WORD _CLK2 :1;
    IO_WORD _CLR :1;
    IO_WORD _MODE :1;
    IO_WORD _STOP :1;
    IO_WORD _IVFE :1;
    IO_WORD _IVF :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _FSEL :1;
    IO_WORD _ECKE :1;
  }bit;
  struct{
    IO_WORD _CLK :3;
  }bitc;
 }TCCS0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CLK0 :1;
    IO_BYTE _CLK1 :1;
    IO_BYTE _CLK2 :1;
    IO_BYTE _CLR :1;
    IO_BYTE _MODE :1;
    IO_BYTE _STOP :1;
    IO_BYTE _IVFE :1;
    IO_BYTE _IVF :1;
  }bit;
  struct{
    IO_BYTE _CLK :3;
  }bitc;
 }TCCSL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _FSEL :1;
    IO_BYTE _ECKE :1;
  }bit;
 }TCCSH0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _T0 :1;
    IO_WORD _T1 :1;
    IO_WORD _T2 :1;
    IO_WORD _T3 :1;
    IO_WORD _T4 :1;
    IO_WORD _T5 :1;
    IO_WORD _T6 :1;
    IO_WORD _T7 :1;
    IO_WORD _T8 :1;
    IO_WORD _T9 :1;
    IO_WORD _T10 :1;
    IO_WORD _T11 :1;
    IO_WORD _T12 :1;
    IO_WORD _T13 :1;
    IO_WORD _T14 :1;
    IO_WORD _T15 :1;
  }bit;
  struct{
    IO_WORD _T :16;
  }bitc;
 }TCDT1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _CLK0 :1;
    IO_WORD _CLK1 :1;
    IO_WORD _CLK2 :1;
    IO_WORD _CLR :1;
    IO_WORD _MODE :1;
    IO_WORD _STOP :1;
    IO_WORD _IVFE :1;
    IO_WORD _IVF :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _FSEL :1;
    IO_WORD _ECKE :1;
  }bit;
  struct{
    IO_WORD _CLK :3;
  }bitc;
 }TCCS1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CLK0 :1;
    IO_BYTE _CLK1 :1;
    IO_BYTE _CLK2 :1;
    IO_BYTE _CLR :1;
    IO_BYTE _MODE :1;
    IO_BYTE _STOP :1;
    IO_BYTE _IVFE :1;
    IO_BYTE _IVF :1;
  }bit;
  struct{
    IO_BYTE _CLK :3;
  }bitc;
 }TCCSL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _FSEL :1;
    IO_BYTE _ECKE :1;
  }bit;
 }TCCSH1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CST0 :1;
    IO_BYTE _CST1 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICE0 :1;
    IO_BYTE _ICE1 :1;
    IO_BYTE _ICP0 :1;
    IO_BYTE _ICP1 :1;
  }bit;
 }OCS0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OTD0 :1;
    IO_BYTE _OTD1 :1;
    IO_BYTE _OTE0 :1;
    IO_BYTE _OTE1 :1;
    IO_BYTE _CMOD0 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _CMOD1 :1;
  }bit;
 }OCS1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _C00 :1;
    IO_WORD _C01 :1;
    IO_WORD _C02 :1;
    IO_WORD _C03 :1;
    IO_WORD _C04 :1;
    IO_WORD _C05 :1;
    IO_WORD _C06 :1;
    IO_WORD _C07 :1;
    IO_WORD _C08 :1;
    IO_WORD _C09 :1;
    IO_WORD _C10 :1;
    IO_WORD _C11 :1;
    IO_WORD _C12 :1;
    IO_WORD _C13 :1;
    IO_WORD _C14 :1;
    IO_WORD _C15 :1;
  }bit;
  struct{
    IO_WORD _C0 :16;
  }bitc;
 }OCCP0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _C00 :1;
    IO_WORD _C01 :1;
    IO_WORD _C02 :1;
    IO_WORD _C03 :1;
    IO_WORD _C04 :1;
    IO_WORD _C05 :1;
    IO_WORD _C06 :1;
    IO_WORD _C07 :1;
    IO_WORD _C08 :1;
    IO_WORD _C09 :1;
    IO_WORD _C10 :1;
    IO_WORD _C11 :1;
    IO_WORD _C12 :1;
    IO_WORD _C13 :1;
    IO_WORD _C14 :1;
    IO_WORD _C15 :1;
  }bit;
  struct{
    IO_WORD _C0 :16;
  }bitc;
 }OCCP1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CST2 :1;
    IO_BYTE _CST3 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICE2 :1;
    IO_BYTE _ICE3 :1;
    IO_BYTE _ICP2 :1;
    IO_BYTE _ICP3 :1;
  }bit;
 }OCS2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OTD2 :1;
    IO_BYTE _OTD3 :1;
    IO_BYTE _OTE2 :1;
    IO_BYTE _OTE3 :1;
    IO_BYTE _CMOD0 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _CMOD1 :1;
  }bit;
 }OCS3STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _C00 :1;
    IO_WORD _C01 :1;
    IO_WORD _C02 :1;
    IO_WORD _C03 :1;
    IO_WORD _C04 :1;
    IO_WORD _C05 :1;
    IO_WORD _C06 :1;
    IO_WORD _C07 :1;
    IO_WORD _C08 :1;
    IO_WORD _C09 :1;
    IO_WORD _C10 :1;
    IO_WORD _C11 :1;
    IO_WORD _C12 :1;
    IO_WORD _C13 :1;
    IO_WORD _C14 :1;
    IO_WORD _C15 :1;
  }bit;
  struct{
    IO_WORD _C0 :16;
  }bitc;
 }OCCP2STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _C00 :1;
    IO_WORD _C01 :1;
    IO_WORD _C02 :1;
    IO_WORD _C03 :1;
    IO_WORD _C04 :1;
    IO_WORD _C05 :1;
    IO_WORD _C06 :1;
    IO_WORD _C07 :1;
    IO_WORD _C08 :1;
    IO_WORD _C09 :1;
    IO_WORD _C10 :1;
    IO_WORD _C11 :1;
    IO_WORD _C12 :1;
    IO_WORD _C13 :1;
    IO_WORD _C14 :1;
    IO_WORD _C15 :1;
  }bit;
  struct{
    IO_WORD _C0 :16;
  }bitc;
 }OCCP3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CST4 :1;
    IO_BYTE _CST5 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICE4 :1;
    IO_BYTE _ICE5 :1;
    IO_BYTE _ICP4 :1;
    IO_BYTE _ICP5 :1;
  }bit;
 }OCS4STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OTD4 :1;
    IO_BYTE _OTD5 :1;
    IO_BYTE _OTE4 :1;
    IO_BYTE _OTE5 :1;
    IO_BYTE _CMOD0 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _CMOD1 :1;
  }bit;
 }OCS5STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _C00 :1;
    IO_WORD _C01 :1;
    IO_WORD _C02 :1;
    IO_WORD _C03 :1;
    IO_WORD _C04 :1;
    IO_WORD _C05 :1;
    IO_WORD _C06 :1;
    IO_WORD _C07 :1;
    IO_WORD _C08 :1;
    IO_WORD _C09 :1;
    IO_WORD _C10 :1;
    IO_WORD _C11 :1;
    IO_WORD _C12 :1;
    IO_WORD _C13 :1;
    IO_WORD _C14 :1;
    IO_WORD _C15 :1;
  }bit;
  struct{
    IO_WORD _C0 :16;
  }bitc;
 }OCCP4STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _C00 :1;
    IO_WORD _C01 :1;
    IO_WORD _C02 :1;
    IO_WORD _C03 :1;
    IO_WORD _C04 :1;
    IO_WORD _C05 :1;
    IO_WORD _C06 :1;
    IO_WORD _C07 :1;
    IO_WORD _C08 :1;
    IO_WORD _C09 :1;
    IO_WORD _C10 :1;
    IO_WORD _C11 :1;
    IO_WORD _C12 :1;
    IO_WORD _C13 :1;
    IO_WORD _C14 :1;
    IO_WORD _C15 :1;
  }bit;
  struct{
    IO_WORD _C0 :16;
  }bitc;
 }OCCP5STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CST6 :1;
    IO_BYTE _CST7 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _ICE6 :1;
    IO_BYTE _ICE7 :1;
    IO_BYTE _ICP6 :1;
    IO_BYTE _ICP7 :1;
  }bit;
 }OCS6STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OTD6 :1;
    IO_BYTE _OTD7 :1;
    IO_BYTE _OTE6 :1;
    IO_BYTE _OTE7 :1;
    IO_BYTE _CMOD0 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _CMOD1 :1;
  }bit;
 }OCS7STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _C00 :1;
    IO_WORD _C01 :1;
    IO_WORD _C02 :1;
    IO_WORD _C03 :1;
    IO_WORD _C04 :1;
    IO_WORD _C05 :1;
    IO_WORD _C06 :1;
    IO_WORD _C07 :1;
    IO_WORD _C08 :1;
    IO_WORD _C09 :1;
    IO_WORD _C10 :1;
    IO_WORD _C11 :1;
    IO_WORD _C12 :1;
    IO_WORD _C13 :1;
    IO_WORD _C14 :1;
    IO_WORD _C15 :1;
  }bit;
  struct{
    IO_WORD _C0 :16;
  }bitc;
 }OCCP6STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _C00 :1;
    IO_WORD _C01 :1;
    IO_WORD _C02 :1;
    IO_WORD _C03 :1;
    IO_WORD _C04 :1;
    IO_WORD _C05 :1;
    IO_WORD _C06 :1;
    IO_WORD _C07 :1;
    IO_WORD _C08 :1;
    IO_WORD _C09 :1;
    IO_WORD _C10 :1;
    IO_WORD _C11 :1;
    IO_WORD _C12 :1;
    IO_WORD _C13 :1;
    IO_WORD _C14 :1;
    IO_WORD _C15 :1;
  }bit;
  struct{
    IO_WORD _C0 :16;
  }bitc;
 }OCCP7STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EG00 :1;
    IO_BYTE _EG01 :1;
    IO_BYTE _EG10 :1;
    IO_BYTE _EG11 :1;
    IO_BYTE _ICE0 :1;
    IO_BYTE _ICE1 :1;
    IO_BYTE _ICP0 :1;
    IO_BYTE _ICP1 :1;
  }bit;
  struct{
    IO_BYTE _EG0 :2;
    IO_BYTE _EG1 :2;
  }bitc;
 }ICS01STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IEI0 :1;
    IO_BYTE _IEI1 :1;
    IO_BYTE _ICUS0 :1;
    IO_BYTE  :1;
    IO_BYTE _ICUS1 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }ICE01STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _CP00 :1;
    IO_WORD _CP01 :1;
    IO_WORD _CP02 :1;
    IO_WORD _CP03 :1;
    IO_WORD _CP04 :1;
    IO_WORD _CP05 :1;
    IO_WORD _CP06 :1;
    IO_WORD _CP07 :1;
    IO_WORD _CP08 :1;
    IO_WORD _CP09 :1;
    IO_WORD _CP10 :1;
    IO_WORD _CP11 :1;
    IO_WORD _CP12 :1;
    IO_WORD _CP13 :1;
    IO_WORD _CP14 :1;
    IO_WORD _CP15 :1;
  }bit;
  struct{
    IO_WORD _CP0 :16;
  }bitc;
 }IPCP0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CP00 :1;
    IO_BYTE _CP01 :1;
    IO_BYTE _CP02 :1;
    IO_BYTE _CP03 :1;
    IO_BYTE _CP04 :1;
    IO_BYTE _CP05 :1;
    IO_BYTE _CP06 :1;
    IO_BYTE _CP07 :1;
  }bit;
 }IPCPL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CP08 :1;
    IO_BYTE _CP09 :1;
    IO_BYTE _CP10 :1;
    IO_BYTE _CP11 :1;
    IO_BYTE _CP12 :1;
    IO_BYTE _CP13 :1;
    IO_BYTE _CP14 :1;
    IO_BYTE _CP15 :1;
  }bit;
 }IPCPH0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _CP00 :1;
    IO_WORD _CP01 :1;
    IO_WORD _CP02 :1;
    IO_WORD _CP03 :1;
    IO_WORD _CP04 :1;
    IO_WORD _CP05 :1;
    IO_WORD _CP06 :1;
    IO_WORD _CP07 :1;
    IO_WORD _CP08 :1;
    IO_WORD _CP09 :1;
    IO_WORD _CP10 :1;
    IO_WORD _CP11 :1;
    IO_WORD _CP12 :1;
    IO_WORD _CP13 :1;
    IO_WORD _CP14 :1;
    IO_WORD _CP15 :1;
  }bit;
  struct{
    IO_WORD _CP0 :16;
  }bitc;
 }IPCP1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CP00 :1;
    IO_BYTE _CP01 :1;
    IO_BYTE _CP02 :1;
    IO_BYTE _CP03 :1;
    IO_BYTE _CP04 :1;
    IO_BYTE _CP05 :1;
    IO_BYTE _CP06 :1;
    IO_BYTE _CP07 :1;
  }bit;
 }IPCPL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CP08 :1;
    IO_BYTE _CP09 :1;
    IO_BYTE _CP10 :1;
    IO_BYTE _CP11 :1;
    IO_BYTE _CP12 :1;
    IO_BYTE _CP13 :1;
    IO_BYTE _CP14 :1;
    IO_BYTE _CP15 :1;
  }bit;
 }IPCPH1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EG20 :1;
    IO_BYTE _EG21 :1;
    IO_BYTE _EG30 :1;
    IO_BYTE _EG31 :1;
    IO_BYTE _ICE2 :1;
    IO_BYTE _ICE3 :1;
    IO_BYTE _ICP2 :1;
    IO_BYTE _ICP3 :1;
  }bit;
  struct{
    IO_BYTE _EG2 :2;
    IO_BYTE _EG3 :2;
  }bitc;
 }ICS23STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IEI2 :1;
    IO_BYTE _IEI3 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }ICE23STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _CP00 :1;
    IO_WORD _CP01 :1;
    IO_WORD _CP02 :1;
    IO_WORD _CP03 :1;
    IO_WORD _CP04 :1;
    IO_WORD _CP05 :1;
    IO_WORD _CP06 :1;
    IO_WORD _CP07 :1;
    IO_WORD _CP08 :1;
    IO_WORD _CP09 :1;
    IO_WORD _CP10 :1;
    IO_WORD _CP11 :1;
    IO_WORD _CP12 :1;
    IO_WORD _CP13 :1;
    IO_WORD _CP14 :1;
    IO_WORD _CP15 :1;
  }bit;
  struct{
    IO_WORD _CP0 :16;
  }bitc;
 }IPCP2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CP00 :1;
    IO_BYTE _CP01 :1;
    IO_BYTE _CP02 :1;
    IO_BYTE _CP03 :1;
    IO_BYTE _CP04 :1;
    IO_BYTE _CP05 :1;
    IO_BYTE _CP06 :1;
    IO_BYTE _CP07 :1;
  }bit;
 }IPCPL2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CP08 :1;
    IO_BYTE _CP09 :1;
    IO_BYTE _CP10 :1;
    IO_BYTE _CP11 :1;
    IO_BYTE _CP12 :1;
    IO_BYTE _CP13 :1;
    IO_BYTE _CP14 :1;
    IO_BYTE _CP15 :1;
  }bit;
 }IPCPH2STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _CP00 :1;
    IO_WORD _CP01 :1;
    IO_WORD _CP02 :1;
    IO_WORD _CP03 :1;
    IO_WORD _CP04 :1;
    IO_WORD _CP05 :1;
    IO_WORD _CP06 :1;
    IO_WORD _CP07 :1;
    IO_WORD _CP08 :1;
    IO_WORD _CP09 :1;
    IO_WORD _CP10 :1;
    IO_WORD _CP11 :1;
    IO_WORD _CP12 :1;
    IO_WORD _CP13 :1;
    IO_WORD _CP14 :1;
    IO_WORD _CP15 :1;
  }bit;
  struct{
    IO_WORD _CP0 :16;
  }bitc;
 }IPCP3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CP00 :1;
    IO_BYTE _CP01 :1;
    IO_BYTE _CP02 :1;
    IO_BYTE _CP03 :1;
    IO_BYTE _CP04 :1;
    IO_BYTE _CP05 :1;
    IO_BYTE _CP06 :1;
    IO_BYTE _CP07 :1;
  }bit;
 }IPCPL3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CP08 :1;
    IO_BYTE _CP09 :1;
    IO_BYTE _CP10 :1;
    IO_BYTE _CP11 :1;
    IO_BYTE _CP12 :1;
    IO_BYTE _CP13 :1;
    IO_BYTE _CP14 :1;
    IO_BYTE _CP15 :1;
  }bit;
 }IPCPH3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EG40 :1;
    IO_BYTE _EG41 :1;
    IO_BYTE _EG50 :1;
    IO_BYTE _EG51 :1;
    IO_BYTE _ICE4 :1;
    IO_BYTE _ICE5 :1;
    IO_BYTE _ICP4 :1;
    IO_BYTE _ICP5 :1;
  }bit;
  struct{
    IO_BYTE _EG4 :2;
    IO_BYTE _EG5 :2;
  }bitc;
 }ICS45STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IEI4 :1;
    IO_BYTE _IEI5 :1;
    IO_BYTE _ICUS4 :1;
    IO_BYTE  :1;
    IO_BYTE _ICUS5 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }ICE45STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _CP00 :1;
    IO_WORD _CP01 :1;
    IO_WORD _CP02 :1;
    IO_WORD _CP03 :1;
    IO_WORD _CP04 :1;
    IO_WORD _CP05 :1;
    IO_WORD _CP06 :1;
    IO_WORD _CP07 :1;
    IO_WORD _CP08 :1;
    IO_WORD _CP09 :1;
    IO_WORD _CP10 :1;
    IO_WORD _CP11 :1;
    IO_WORD _CP12 :1;
    IO_WORD _CP13 :1;
    IO_WORD _CP14 :1;
    IO_WORD _CP15 :1;
  }bit;
  struct{
    IO_WORD _CP0 :16;
  }bitc;
 }IPCP4STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CP00 :1;
    IO_BYTE _CP01 :1;
    IO_BYTE _CP02 :1;
    IO_BYTE _CP03 :1;
    IO_BYTE _CP04 :1;
    IO_BYTE _CP05 :1;
    IO_BYTE _CP06 :1;
    IO_BYTE _CP07 :1;
  }bit;
 }IPCPL4STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CP08 :1;
    IO_BYTE _CP09 :1;
    IO_BYTE _CP10 :1;
    IO_BYTE _CP11 :1;
    IO_BYTE _CP12 :1;
    IO_BYTE _CP13 :1;
    IO_BYTE _CP14 :1;
    IO_BYTE _CP15 :1;
  }bit;
 }IPCPH4STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _CP00 :1;
    IO_WORD _CP01 :1;
    IO_WORD _CP02 :1;
    IO_WORD _CP03 :1;
    IO_WORD _CP04 :1;
    IO_WORD _CP05 :1;
    IO_WORD _CP06 :1;
    IO_WORD _CP07 :1;
    IO_WORD _CP08 :1;
    IO_WORD _CP09 :1;
    IO_WORD _CP10 :1;
    IO_WORD _CP11 :1;
    IO_WORD _CP12 :1;
    IO_WORD _CP13 :1;
    IO_WORD _CP14 :1;
    IO_WORD _CP15 :1;
  }bit;
  struct{
    IO_WORD _CP0 :16;
  }bitc;
 }IPCP5STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CP00 :1;
    IO_BYTE _CP01 :1;
    IO_BYTE _CP02 :1;
    IO_BYTE _CP03 :1;
    IO_BYTE _CP04 :1;
    IO_BYTE _CP05 :1;
    IO_BYTE _CP06 :1;
    IO_BYTE _CP07 :1;
  }bit;
 }IPCPL5STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CP08 :1;
    IO_BYTE _CP09 :1;
    IO_BYTE _CP10 :1;
    IO_BYTE _CP11 :1;
    IO_BYTE _CP12 :1;
    IO_BYTE _CP13 :1;
    IO_BYTE _CP14 :1;
    IO_BYTE _CP15 :1;
  }bit;
 }IPCPH5STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EG60 :1;
    IO_BYTE _EG61 :1;
    IO_BYTE _EG70 :1;
    IO_BYTE _EG71 :1;
    IO_BYTE _ICE6 :1;
    IO_BYTE _ICE7 :1;
    IO_BYTE _ICP6 :1;
    IO_BYTE _ICP7 :1;
  }bit;
  struct{
    IO_BYTE _EG6 :2;
    IO_BYTE _EG7 :2;
  }bitc;
 }ICS67STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IEI6 :1;
    IO_BYTE _IEI7 :1;
    IO_BYTE _ICUS6 :1;
    IO_BYTE  :1;
    IO_BYTE _ICUS7 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }ICE67STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _CP00 :1;
    IO_WORD _CP01 :1;
    IO_WORD _CP02 :1;
    IO_WORD _CP03 :1;
    IO_WORD _CP04 :1;
    IO_WORD _CP05 :1;
    IO_WORD _CP06 :1;
    IO_WORD _CP07 :1;
    IO_WORD _CP08 :1;
    IO_WORD _CP09 :1;
    IO_WORD _CP10 :1;
    IO_WORD _CP11 :1;
    IO_WORD _CP12 :1;
    IO_WORD _CP13 :1;
    IO_WORD _CP14 :1;
    IO_WORD _CP15 :1;
  }bit;
  struct{
    IO_WORD _CP0 :16;
  }bitc;
 }IPCP6STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CP00 :1;
    IO_BYTE _CP01 :1;
    IO_BYTE _CP02 :1;
    IO_BYTE _CP03 :1;
    IO_BYTE _CP04 :1;
    IO_BYTE _CP05 :1;
    IO_BYTE _CP06 :1;
    IO_BYTE _CP07 :1;
  }bit;
 }IPCPL6STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CP08 :1;
    IO_BYTE _CP09 :1;
    IO_BYTE _CP10 :1;
    IO_BYTE _CP11 :1;
    IO_BYTE _CP12 :1;
    IO_BYTE _CP13 :1;
    IO_BYTE _CP14 :1;
    IO_BYTE _CP15 :1;
  }bit;
 }IPCPH6STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _CP00 :1;
    IO_WORD _CP01 :1;
    IO_WORD _CP02 :1;
    IO_WORD _CP03 :1;
    IO_WORD _CP04 :1;
    IO_WORD _CP05 :1;
    IO_WORD _CP06 :1;
    IO_WORD _CP07 :1;
    IO_WORD _CP08 :1;
    IO_WORD _CP09 :1;
    IO_WORD _CP10 :1;
    IO_WORD _CP11 :1;
    IO_WORD _CP12 :1;
    IO_WORD _CP13 :1;
    IO_WORD _CP14 :1;
    IO_WORD _CP15 :1;
  }bit;
  struct{
    IO_WORD _CP0 :16;
  }bitc;
 }IPCP7STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CP00 :1;
    IO_BYTE _CP01 :1;
    IO_BYTE _CP02 :1;
    IO_BYTE _CP03 :1;
    IO_BYTE _CP04 :1;
    IO_BYTE _CP05 :1;
    IO_BYTE _CP06 :1;
    IO_BYTE _CP07 :1;
  }bit;
 }IPCPL7STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CP08 :1;
    IO_BYTE _CP09 :1;
    IO_BYTE _CP10 :1;
    IO_BYTE _CP11 :1;
    IO_BYTE _CP12 :1;
    IO_BYTE _CP13 :1;
    IO_BYTE _CP14 :1;
    IO_BYTE _CP15 :1;
  }bit;
 }IPCPH7STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EN0 :1;
    IO_BYTE _EN1 :1;
    IO_BYTE _EN2 :1;
    IO_BYTE _EN3 :1;
    IO_BYTE _EN4 :1;
    IO_BYTE _EN5 :1;
    IO_BYTE _EN6 :1;
    IO_BYTE _EN7 :1;
  }bit;
 }ENIR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ER0 :1;
    IO_BYTE _ER1 :1;
    IO_BYTE _ER2 :1;
    IO_BYTE _ER3 :1;
    IO_BYTE _ER4 :1;
    IO_BYTE _ER5 :1;
    IO_BYTE _ER6 :1;
    IO_BYTE _ER7 :1;
  }bit;
 }EIRR0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _LA0 :1;
    IO_WORD _LB0 :1;
    IO_WORD _LA1 :1;
    IO_WORD _LB1 :1;
    IO_WORD _LA2 :1;
    IO_WORD _LB2 :1;
    IO_WORD _LA3 :1;
    IO_WORD _LB3 :1;
    IO_WORD _LA4 :1;
    IO_WORD _LB4 :1;
    IO_WORD _LA5 :1;
    IO_WORD _LB5 :1;
    IO_WORD _LA6 :1;
    IO_WORD _LB6 :1;
    IO_WORD _LA7 :1;
    IO_WORD _LB7 :1;
  }bit;
 }ELVR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _LA0 :1;
    IO_BYTE _LB0 :1;
    IO_BYTE _LA1 :1;
    IO_BYTE _LB1 :1;
    IO_BYTE _LA2 :1;
    IO_BYTE _LB2 :1;
    IO_BYTE _LA3 :1;
    IO_BYTE _LB3 :1;
  }bit;
 }ELVRL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _LA4 :1;
    IO_BYTE _LB4 :1;
    IO_BYTE _LA5 :1;
    IO_BYTE _LB5 :1;
    IO_BYTE _LA6 :1;
    IO_BYTE _LB6 :1;
    IO_BYTE _LA7 :1;
    IO_BYTE _LB7 :1;
  }bit;
 }ELVRH0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EN8 :1;
    IO_BYTE _EN9 :1;
    IO_BYTE _EN10 :1;
    IO_BYTE _EN11 :1;
    IO_BYTE _EN12 :1;
    IO_BYTE _EN13 :1;
    IO_BYTE _EN14 :1;
    IO_BYTE _EN15 :1;
  }bit;
 }ENIR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ER8 :1;
    IO_BYTE _ER9 :1;
    IO_BYTE _ER10 :1;
    IO_BYTE _ER11 :1;
    IO_BYTE _ER12 :1;
    IO_BYTE _ER13 :1;
    IO_BYTE _ER14 :1;
    IO_BYTE _ER15 :1;
  }bit;
 }EIRR1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _LA8 :1;
    IO_WORD _LB8 :1;
    IO_WORD _LA9 :1;
    IO_WORD _LB9 :1;
    IO_WORD _LA10 :1;
    IO_WORD _LB10 :1;
    IO_WORD _LA11 :1;
    IO_WORD _LB11 :1;
    IO_WORD _LA12 :1;
    IO_WORD _LB12 :1;
    IO_WORD _LA13 :1;
    IO_WORD _LB13 :1;
    IO_WORD _LA14 :1;
    IO_WORD _LB14 :1;
    IO_WORD _LA15 :1;
    IO_WORD _LB15 :1;
  }bit;
 }ELVR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _LA8 :1;
    IO_BYTE _LB8 :1;
    IO_BYTE _LA9 :1;
    IO_BYTE _LB9 :1;
    IO_BYTE _LA10 :1;
    IO_BYTE _LB10 :1;
    IO_BYTE _LA11 :1;
    IO_BYTE _LB11 :1;
  }bit;
 }ELVRL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _LA12 :1;
    IO_BYTE _LB12 :1;
    IO_BYTE _LA13 :1;
    IO_BYTE _LB13 :1;
    IO_BYTE _LA14 :1;
    IO_BYTE _LB14 :1;
    IO_BYTE _LA15 :1;
    IO_BYTE _LB15 :1;
  }bit;
 }ELVRH1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TRG :1;
    IO_WORD _CNTE :1;
    IO_WORD _UF :1;
    IO_WORD _INTE :1;
    IO_WORD _RELD :1;
    IO_WORD _OUTL :1;
    IO_WORD _OUTE :1;
    IO_WORD _MOD0 :1;
    IO_WORD _MOD1 :1;
    IO_WORD _MOD2 :1;
    IO_WORD _CSL0 :1;
    IO_WORD _CSL1 :1;
    IO_WORD _FSEL :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD :10;
    IO_WORD _CSL :2;
  }bitc;
 }TMCSR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TRG :1;
    IO_BYTE _CNTE :1;
    IO_BYTE _UF :1;
    IO_BYTE _INTE :1;
    IO_BYTE _RELD :1;
    IO_BYTE _OUTL :1;
    IO_BYTE _OUTE :1;
    IO_BYTE _MOD0 :1;
  }bit;
 }TMCSRL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MOD1 :1;
    IO_BYTE _MOD2 :1;
    IO_BYTE _CSL0 :1;
    IO_BYTE _CSL1 :1;
    IO_BYTE _FSEL :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CSL :2;
  }bitc;
 }TMCSRH0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TRG :1;
    IO_WORD _CNTE :1;
    IO_WORD _UF :1;
    IO_WORD _INTE :1;
    IO_WORD _RELD :1;
    IO_WORD _OUTL :1;
    IO_WORD _OUTE :1;
    IO_WORD _MOD0 :1;
    IO_WORD _MOD1 :1;
    IO_WORD _MOD2 :1;
    IO_WORD _CSL0 :1;
    IO_WORD _CSL1 :1;
    IO_WORD _FSEL :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD :10;
    IO_WORD _CSL :2;
  }bitc;
 }TMCSR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TRG :1;
    IO_BYTE _CNTE :1;
    IO_BYTE _UF :1;
    IO_BYTE _INTE :1;
    IO_BYTE _RELD :1;
    IO_BYTE _OUTL :1;
    IO_BYTE _OUTE :1;
    IO_BYTE _MOD0 :1;
  }bit;
 }TMCSRL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MOD1 :1;
    IO_BYTE _MOD2 :1;
    IO_BYTE _CSL0 :1;
    IO_BYTE _CSL1 :1;
    IO_BYTE _FSEL :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CSL :2;
  }bitc;
 }TMCSRH1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TRG :1;
    IO_WORD _CNTE :1;
    IO_WORD _UF :1;
    IO_WORD _INTE :1;
    IO_WORD _RELD :1;
    IO_WORD _OUTL :1;
    IO_WORD _OUTE :1;
    IO_WORD _MOD0 :1;
    IO_WORD _MOD1 :1;
    IO_WORD _MOD2 :1;
    IO_WORD _CSL0 :1;
    IO_WORD _CSL1 :1;
    IO_WORD _FSEL :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD :10;
    IO_WORD _CSL :2;
  }bitc;
 }TMCSR2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TRG :1;
    IO_BYTE _CNTE :1;
    IO_BYTE _UF :1;
    IO_BYTE _INTE :1;
    IO_BYTE _RELD :1;
    IO_BYTE _OUTL :1;
    IO_BYTE _OUTE :1;
    IO_BYTE _MOD0 :1;
  }bit;
 }TMCSRL2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MOD1 :1;
    IO_BYTE _MOD2 :1;
    IO_BYTE _CSL0 :1;
    IO_BYTE _CSL1 :1;
    IO_BYTE _FSEL :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CSL :2;
  }bitc;
 }TMCSRH2STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TRG :1;
    IO_WORD _CNTE :1;
    IO_WORD _UF :1;
    IO_WORD _INTE :1;
    IO_WORD _RELD :1;
    IO_WORD _OUTL :1;
    IO_WORD _OUTE :1;
    IO_WORD _MOD0 :1;
    IO_WORD _MOD1 :1;
    IO_WORD _MOD2 :1;
    IO_WORD _CSL0 :1;
    IO_WORD _CSL1 :1;
    IO_WORD _FSEL :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD :10;
    IO_WORD _CSL :2;
  }bitc;
 }TMCSR3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TRG :1;
    IO_BYTE _CNTE :1;
    IO_BYTE _UF :1;
    IO_BYTE _INTE :1;
    IO_BYTE _RELD :1;
    IO_BYTE _OUTL :1;
    IO_BYTE _OUTE :1;
    IO_BYTE _MOD0 :1;
  }bit;
 }TMCSRL3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MOD1 :1;
    IO_BYTE _MOD2 :1;
    IO_BYTE _CSL0 :1;
    IO_BYTE _CSL1 :1;
    IO_BYTE _FSEL :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CSL :2;
  }bitc;
 }TMCSRH3STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TRG :1;
    IO_WORD _CNTE :1;
    IO_WORD _UF :1;
    IO_WORD _INTE :1;
    IO_WORD _RELD :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _MOD0 :1;
    IO_WORD _MOD1 :1;
    IO_WORD _MOD2 :1;
    IO_WORD _CSL0 :1;
    IO_WORD _CSL1 :1;
    IO_WORD _FSEL :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD :10;
    IO_WORD _CSL :2;
  }bitc;
 }TMCSR6STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TRG :1;
    IO_BYTE _CNTE :1;
    IO_BYTE _UF :1;
    IO_BYTE _INTE :1;
    IO_BYTE _RELD :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _MOD0 :1;
  }bit;
 }TMCSRL6STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MOD1 :1;
    IO_BYTE _MOD2 :1;
    IO_BYTE _CSL0 :1;
    IO_BYTE _CSL1 :1;
    IO_BYTE _FSEL :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CSL :2;
  }bitc;
 }TMCSRH6STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TSEL00 :1;
    IO_WORD _TSEL01 :1;
    IO_WORD _TSEL02 :1;
    IO_WORD _TSEL03 :1;
    IO_WORD _TSEL10 :1;
    IO_WORD _TSEL11 :1;
    IO_WORD _TSEL12 :1;
    IO_WORD _TSEL13 :1;
    IO_WORD _TSEL20 :1;
    IO_WORD _TSEL21 :1;
    IO_WORD _TSEL22 :1;
    IO_WORD _TSEL23 :1;
    IO_WORD _TSEL30 :1;
    IO_WORD _TSEL31 :1;
    IO_WORD _TSEL32 :1;
    IO_WORD _TSEL33 :1;
  }bit;
  struct{
    IO_WORD _TSEL0 :4;
    IO_WORD _TSEL1 :4;
    IO_WORD _TSEL2 :4;
    IO_WORD _TSEL3 :4;
  }bitc;
 }GCN10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TSEL00 :1;
    IO_BYTE _TSEL01 :1;
    IO_BYTE _TSEL02 :1;
    IO_BYTE _TSEL03 :1;
    IO_BYTE _TSEL10 :1;
    IO_BYTE _TSEL11 :1;
    IO_BYTE _TSEL12 :1;
    IO_BYTE _TSEL13 :1;
  }bit;
  struct{
    IO_BYTE _TSEL0 :4;
    IO_BYTE _TSEL1 :4;
  }bitc;
 }GCN1L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TSEL20 :1;
    IO_BYTE _TSEL21 :1;
    IO_BYTE _TSEL22 :1;
    IO_BYTE _TSEL23 :1;
    IO_BYTE _TSEL30 :1;
    IO_BYTE _TSEL31 :1;
    IO_BYTE _TSEL32 :1;
    IO_BYTE _TSEL33 :1;
  }bit;
  struct{
    IO_BYTE _TSEL2 :4;
    IO_BYTE _TSEL3 :4;
  }bitc;
 }GCN1H0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _EN0 :1;
    IO_WORD _EN1 :1;
    IO_WORD _EN2 :1;
    IO_WORD _EN3 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _CKSEL0 :1;
    IO_WORD _CKSEL1 :1;
    IO_WORD _CKSEL2 :1;
    IO_WORD _CKSEL3 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD _EN :4;
    IO_WORD :4;
    IO_WORD _CKSEL :4;
  }bitc;
 }GCN20STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EN0 :1;
    IO_BYTE _EN1 :1;
    IO_BYTE _EN2 :1;
    IO_BYTE _EN3 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _EN :4;
  }bitc;
 }GCN2L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CKSEL0 :1;
    IO_BYTE _CKSEL1 :1;
    IO_BYTE _CKSEL2 :1;
    IO_BYTE _CKSEL3 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _CKSEL :4;
  }bitc;
 }GCN2H0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PTMR0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PCSR0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PDUT0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _OSEL :1;
    IO_WORD _OE :1;
    IO_WORD _IRS0 :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRQF :1;
    IO_WORD _IREN :1;
    IO_WORD _EGS0 :1;
    IO_WORD _EGS1 :1;
    IO_WORD  :1;
    IO_WORD _PGMS :1;
    IO_WORD _CKS0 :1;
    IO_WORD _CKS1 :1;
    IO_WORD _RTRG :1;
    IO_WORD _MDSE :1;
    IO_WORD _STGR :1;
    IO_WORD _CNTE :1;
  }bit;
  struct{
    IO_WORD :2;
    IO_WORD _IRS :2;
    IO_WORD :2;
    IO_WORD _EGS :2;
    IO_WORD :2;
    IO_WORD _CKS :2;
  }bitc;
 }PCN0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OSEL :1;
    IO_BYTE _OE :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IREN :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _EGS1 :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _IRS :2;
    IO_BYTE :2;
    IO_BYTE _EGS :2;
  }bitc;
 }PCNL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE _PGMS :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _CNTE :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PTMR1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PCSR1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PDUT1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _OSEL :1;
    IO_WORD _OE :1;
    IO_WORD _IRS0 :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRQF :1;
    IO_WORD _IREN :1;
    IO_WORD _EGS0 :1;
    IO_WORD _EGS1 :1;
    IO_WORD  :1;
    IO_WORD _PGMS :1;
    IO_WORD _CKS0 :1;
    IO_WORD _CKS1 :1;
    IO_WORD _RTRG :1;
    IO_WORD _MDSE :1;
    IO_WORD _STGR :1;
    IO_WORD _CNTE :1;
  }bit;
  struct{
    IO_WORD :2;
    IO_WORD _IRS :2;
    IO_WORD :2;
    IO_WORD _EGS :2;
    IO_WORD :2;
    IO_WORD _CKS :2;
  }bitc;
 }PCN1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OSEL :1;
    IO_BYTE _OE :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IREN :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _EGS1 :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _IRS :2;
    IO_BYTE :2;
    IO_BYTE _EGS :2;
  }bitc;
 }PCNL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE _PGMS :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _CNTE :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PTMR2STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PCSR2STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PDUT2STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _OSEL :1;
    IO_WORD _OE :1;
    IO_WORD _IRS0 :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRQF :1;
    IO_WORD _IREN :1;
    IO_WORD _EGS0 :1;
    IO_WORD _EGS1 :1;
    IO_WORD  :1;
    IO_WORD _PGMS :1;
    IO_WORD _CKS0 :1;
    IO_WORD _CKS1 :1;
    IO_WORD _RTRG :1;
    IO_WORD _MDSE :1;
    IO_WORD _STGR :1;
    IO_WORD _CNTE :1;
  }bit;
  struct{
    IO_WORD :2;
    IO_WORD _IRS :2;
    IO_WORD :2;
    IO_WORD _EGS :2;
    IO_WORD :2;
    IO_WORD _CKS :2;
  }bitc;
 }PCN2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OSEL :1;
    IO_BYTE _OE :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IREN :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _EGS1 :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _IRS :2;
    IO_BYTE :2;
    IO_BYTE _EGS :2;
  }bitc;
 }PCNL2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE _PGMS :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _CNTE :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH2STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PTMR3STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PCSR3STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PDUT3STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _OSEL :1;
    IO_WORD _OE :1;
    IO_WORD _IRS0 :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRQF :1;
    IO_WORD _IREN :1;
    IO_WORD _EGS0 :1;
    IO_WORD _EGS1 :1;
    IO_WORD  :1;
    IO_WORD _PGMS :1;
    IO_WORD _CKS0 :1;
    IO_WORD _CKS1 :1;
    IO_WORD _RTRG :1;
    IO_WORD _MDSE :1;
    IO_WORD _STGR :1;
    IO_WORD _CNTE :1;
  }bit;
  struct{
    IO_WORD :2;
    IO_WORD _IRS :2;
    IO_WORD :2;
    IO_WORD _EGS :2;
    IO_WORD :2;
    IO_WORD _CKS :2;
  }bitc;
 }PCN3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OSEL :1;
    IO_BYTE _OE :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IREN :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _EGS1 :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _IRS :2;
    IO_BYTE :2;
    IO_BYTE _EGS :2;
  }bitc;
 }PCNL3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE _PGMS :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _CNTE :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH3STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TSEL00 :1;
    IO_WORD _TSEL01 :1;
    IO_WORD _TSEL02 :1;
    IO_WORD _TSEL03 :1;
    IO_WORD _TSEL10 :1;
    IO_WORD _TSEL11 :1;
    IO_WORD _TSEL12 :1;
    IO_WORD _TSEL13 :1;
    IO_WORD _TSEL20 :1;
    IO_WORD _TSEL21 :1;
    IO_WORD _TSEL22 :1;
    IO_WORD _TSEL23 :1;
    IO_WORD _TSEL30 :1;
    IO_WORD _TSEL31 :1;
    IO_WORD _TSEL32 :1;
    IO_WORD _TSEL33 :1;
  }bit;
  struct{
    IO_WORD _TSEL0 :4;
    IO_WORD _TSEL1 :4;
    IO_WORD _TSEL2 :4;
    IO_WORD _TSEL3 :4;
  }bitc;
 }GCN11STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TSEL00 :1;
    IO_BYTE _TSEL01 :1;
    IO_BYTE _TSEL02 :1;
    IO_BYTE _TSEL03 :1;
    IO_BYTE _TSEL10 :1;
    IO_BYTE _TSEL11 :1;
    IO_BYTE _TSEL12 :1;
    IO_BYTE _TSEL13 :1;
  }bit;
  struct{
    IO_BYTE _TSEL0 :4;
    IO_BYTE _TSEL1 :4;
  }bitc;
 }GCN1L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TSEL20 :1;
    IO_BYTE _TSEL21 :1;
    IO_BYTE _TSEL22 :1;
    IO_BYTE _TSEL23 :1;
    IO_BYTE _TSEL30 :1;
    IO_BYTE _TSEL31 :1;
    IO_BYTE _TSEL32 :1;
    IO_BYTE _TSEL33 :1;
  }bit;
  struct{
    IO_BYTE _TSEL2 :4;
    IO_BYTE _TSEL3 :4;
  }bitc;
 }GCN1H1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _EN0 :1;
    IO_WORD _EN1 :1;
    IO_WORD _EN2 :1;
    IO_WORD _EN3 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _CKSEL0 :1;
    IO_WORD _CKSEL1 :1;
    IO_WORD _CKSEL2 :1;
    IO_WORD _CKSEL3 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD :8;
    IO_WORD _CKSEL :4;
  }bitc;
 }GCN21STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EN0 :1;
    IO_BYTE _EN1 :1;
    IO_BYTE _EN2 :1;
    IO_BYTE _EN3 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }GCN2L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CKSEL0 :1;
    IO_BYTE _CKSEL1 :1;
    IO_BYTE _CKSEL2 :1;
    IO_BYTE _CKSEL3 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _CKSEL :4;
  }bitc;
 }GCN2H1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PTMR4STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PCSR4STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PDUT4STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _OSEL :1;
    IO_WORD _OE :1;
    IO_WORD _IRS0 :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRQF :1;
    IO_WORD _IREN :1;
    IO_WORD _EGS0 :1;
    IO_WORD _EGS1 :1;
    IO_WORD  :1;
    IO_WORD _PGMS :1;
    IO_WORD _CKS0 :1;
    IO_WORD _CKS1 :1;
    IO_WORD _RTRG :1;
    IO_WORD _MDSE :1;
    IO_WORD _STGR :1;
    IO_WORD _CNTE :1;
  }bit;
  struct{
    IO_WORD :2;
    IO_WORD _IRS :2;
    IO_WORD :2;
    IO_WORD _EGS :2;
    IO_WORD :2;
    IO_WORD _CKS :2;
  }bitc;
 }PCN4STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OSEL :1;
    IO_BYTE _OE :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IREN :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _EGS1 :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _IRS :2;
    IO_BYTE :2;
    IO_BYTE _EGS :2;
  }bitc;
 }PCNL4STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE _PGMS :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _CNTE :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH4STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PTMR5STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PCSR5STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PDUT5STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _OSEL :1;
    IO_WORD _OE :1;
    IO_WORD _IRS0 :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRQF :1;
    IO_WORD _IREN :1;
    IO_WORD _EGS0 :1;
    IO_WORD _EGS1 :1;
    IO_WORD  :1;
    IO_WORD _PGMS :1;
    IO_WORD _CKS0 :1;
    IO_WORD _CKS1 :1;
    IO_WORD _RTRG :1;
    IO_WORD _MDSE :1;
    IO_WORD _STGR :1;
    IO_WORD _CNTE :1;
  }bit;
  struct{
    IO_WORD :2;
    IO_WORD _IRS :2;
    IO_WORD :2;
    IO_WORD _EGS :2;
    IO_WORD :2;
    IO_WORD _CKS :2;
  }bitc;
 }PCN5STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OSEL :1;
    IO_BYTE _OE :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IREN :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _EGS1 :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _IRS :2;
    IO_BYTE :2;
    IO_BYTE _EGS :2;
  }bitc;
 }PCNL5STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE _PGMS :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _CNTE :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH5STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ADT :1;
    IO_BYTE _GCA :1;
    IO_BYTE _AAS :1;
    IO_BYTE _TRX :1;
    IO_BYTE _LRB :1;
    IO_BYTE _AL :1;
    IO_BYTE _RSC :1;
    IO_BYTE _BB :1;
  }bit;
 }IBSR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INT :1;
    IO_BYTE _INTE :1;
    IO_BYTE _GCAA :1;
    IO_BYTE _ACK :1;
    IO_BYTE _MSS :1;
    IO_BYTE _SCC :1;
    IO_BYTE _BEIE :1;
    IO_BYTE _BER :1;
  }bit;
 }IBCR0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TA0 :1;
    IO_WORD _TA1 :1;
    IO_WORD _TA2 :1;
    IO_WORD _TA3 :1;
    IO_WORD _TA4 :1;
    IO_WORD _TA5 :1;
    IO_WORD _TA6 :1;
    IO_WORD _TA7 :1;
    IO_WORD _TA8 :1;
    IO_WORD _TA9 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD _TA :10;
  }bitc;
 }ITBA0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TA0 :1;
    IO_BYTE _TA1 :1;
    IO_BYTE _TA2 :1;
    IO_BYTE _TA3 :1;
    IO_BYTE _TA4 :1;
    IO_BYTE _TA5 :1;
    IO_BYTE _TA6 :1;
    IO_BYTE _TA7 :1;
  }bit;
 }ITBAL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TA8 :1;
    IO_BYTE _TA9 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }ITBAH0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TM0 :1;
    IO_WORD _TM1 :1;
    IO_WORD _TM2 :1;
    IO_WORD _TM3 :1;
    IO_WORD _TM4 :1;
    IO_WORD _TM5 :1;
    IO_WORD _TM6 :1;
    IO_WORD _TM7 :1;
    IO_WORD _TM8 :1;
    IO_WORD _TM9 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _RAL :1;
    IO_WORD _ENTB :1;
  }bit;
  struct{
    IO_WORD _TM :10;
  }bitc;
 }ITMK0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TM0 :1;
    IO_BYTE _TM1 :1;
    IO_BYTE _TM2 :1;
    IO_BYTE _TM3 :1;
    IO_BYTE _TM4 :1;
    IO_BYTE _TM5 :1;
    IO_BYTE _TM6 :1;
    IO_BYTE _TM7 :1;
  }bit;
 }ITMKL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TM8 :1;
    IO_BYTE _TM9 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _RAL :1;
    IO_BYTE _ENTB :1;
  }bit;
 }ITMKH0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SA0 :1;
    IO_BYTE _SA1 :1;
    IO_BYTE _SA2 :1;
    IO_BYTE _SA3 :1;
    IO_BYTE _SA4 :1;
    IO_BYTE _SA5 :1;
    IO_BYTE _SA6 :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _SA :7;
  }bitc;
 }ISBA0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SM0 :1;
    IO_BYTE _SM1 :1;
    IO_BYTE _SM2 :1;
    IO_BYTE _SM3 :1;
    IO_BYTE _SM4 :1;
    IO_BYTE _SM5 :1;
    IO_BYTE _SM6 :1;
    IO_BYTE _ENSB :1;
  }bit;
  struct{
    IO_BYTE _SM :7;
  }bitc;
 }ISMK0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _D0 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D7 :1;
  }bit;
 }IDAR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CS0 :1;
    IO_BYTE _CS1 :1;
    IO_BYTE _CS2 :1;
    IO_BYTE _CS3 :1;
    IO_BYTE _CS4 :1;
    IO_BYTE _EN :1;
    IO_BYTE _NSF :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _CS :5;
  }bitc;
 }ICCR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ADT :1;
    IO_BYTE _GCA :1;
    IO_BYTE _AAS :1;
    IO_BYTE _TRX :1;
    IO_BYTE _LRB :1;
    IO_BYTE _AL :1;
    IO_BYTE _RSC :1;
    IO_BYTE _BB :1;
  }bit;
 }IBSR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INT :1;
    IO_BYTE _INTE :1;
    IO_BYTE _GCAA :1;
    IO_BYTE _ACK :1;
    IO_BYTE _MSS :1;
    IO_BYTE _SCC :1;
    IO_BYTE _BEIE :1;
    IO_BYTE _BER :1;
  }bit;
 }IBCR1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TA0 :1;
    IO_WORD _TA1 :1;
    IO_WORD _TA2 :1;
    IO_WORD _TA3 :1;
    IO_WORD _TA4 :1;
    IO_WORD _TA5 :1;
    IO_WORD _TA6 :1;
    IO_WORD _TA7 :1;
    IO_WORD _TA8 :1;
    IO_WORD _TA9 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD _TA :10;
  }bitc;
 }ITBA1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TA0 :1;
    IO_BYTE _TA1 :1;
    IO_BYTE _TA2 :1;
    IO_BYTE _TA3 :1;
    IO_BYTE _TA4 :1;
    IO_BYTE _TA5 :1;
    IO_BYTE _TA6 :1;
    IO_BYTE _TA7 :1;
  }bit;
 }ITBAL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TA8 :1;
    IO_BYTE _TA9 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }ITBAH1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TM0 :1;
    IO_WORD _TM1 :1;
    IO_WORD _TM2 :1;
    IO_WORD _TM3 :1;
    IO_WORD _TM4 :1;
    IO_WORD _TM5 :1;
    IO_WORD _TM6 :1;
    IO_WORD _TM7 :1;
    IO_WORD _TM8 :1;
    IO_WORD _TM9 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _RAL :1;
    IO_WORD _ENTB :1;
  }bit;
  struct{
    IO_WORD _TM :10;
  }bitc;
 }ITMK1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TM0 :1;
    IO_BYTE _TM1 :1;
    IO_BYTE _TM2 :1;
    IO_BYTE _TM3 :1;
    IO_BYTE _TM4 :1;
    IO_BYTE _TM5 :1;
    IO_BYTE _TM6 :1;
    IO_BYTE _TM7 :1;
  }bit;
 }ITMKL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TM8 :1;
    IO_BYTE _TM9 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _RAL :1;
    IO_BYTE _ENTB :1;
  }bit;
 }ITMKH1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SA0 :1;
    IO_BYTE _SA1 :1;
    IO_BYTE _SA2 :1;
    IO_BYTE _SA3 :1;
    IO_BYTE _SA4 :1;
    IO_BYTE _SA5 :1;
    IO_BYTE _SA6 :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _SA :7;
  }bitc;
 }ISBA1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SM0 :1;
    IO_BYTE _SM1 :1;
    IO_BYTE _SM2 :1;
    IO_BYTE _SM3 :1;
    IO_BYTE _SM4 :1;
    IO_BYTE _SM5 :1;
    IO_BYTE _SM6 :1;
    IO_BYTE _ENSB :1;
  }bit;
  struct{
    IO_BYTE _SM :7;
  }bitc;
 }ISMK1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _D0 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D7 :1;
  }bit;
 }IDAR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CS0 :1;
    IO_BYTE _CS1 :1;
    IO_BYTE _CS2 :1;
    IO_BYTE _CS3 :1;
    IO_BYTE _CS4 :1;
    IO_BYTE _EN :1;
    IO_BYTE _NSF :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _CS :5;
  }bitc;
 }ICCR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SOE :1;
    IO_BYTE _SCKE :1;
    IO_BYTE _UPCL :1;
    IO_BYTE _REST :1;
    IO_BYTE _EXT :1;
    IO_BYTE _OTO :1;
    IO_BYTE _MD0 :1;
    IO_BYTE _MD1 :1;
  }bit;
  struct{
    IO_BYTE :6;
    IO_BYTE _MD :2;
  }bitc;
 }SMR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TXE :1;
    IO_BYTE _RXE :1;
    IO_BYTE _CRE :1;
    IO_BYTE _AD :1;
    IO_BYTE _CL :1;
    IO_BYTE _SBL :1;
    IO_BYTE _P :1;
    IO_BYTE _PEN :1;
  }bit;
 }SCR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TIE :1;
    IO_BYTE _RIE :1;
    IO_BYTE _BDS :1;
    IO_BYTE _TDRE :1;
    IO_BYTE _RDRF :1;
    IO_BYTE _FRE :1;
    IO_BYTE _ORE :1;
    IO_BYTE _PE :1;
  }bit;
 }SSR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TBI :1;
    IO_BYTE _RBI :1;
    IO_BYTE _BIE :1;
    IO_BYTE _SSM :1;
    IO_BYTE _SCDE :1;
    IO_BYTE _MS :1;
    IO_BYTE _LBR :1;
    IO_BYTE _INV :1;
  }bit;
 }ECCR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SCES :1;
    IO_BYTE _CCO :1;
    IO_BYTE _SIOP :1;
    IO_BYTE _SOPE :1;
    IO_BYTE _LBL0 :1;
    IO_BYTE _LBL1 :1;
    IO_BYTE _LBD :1;
    IO_BYTE _LBIE :1;
  }bit;
  struct{
    IO_BYTE :4;
    IO_BYTE _LBL :2;
  }bitc;
 }ESCR0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _BGR0 :1;
    IO_WORD _BGR1 :1;
    IO_WORD _BGR2 :1;
    IO_WORD _BGR3 :1;
    IO_WORD _BGR4 :1;
    IO_WORD _BGR5 :1;
    IO_WORD _BGR6 :1;
    IO_WORD _BGR7 :1;
    IO_WORD _BGR8 :1;
    IO_WORD _BGR9 :1;
    IO_WORD _BGR10 :1;
    IO_WORD _BGR11 :1;
    IO_WORD _BGR12 :1;
    IO_WORD _BGR13 :1;
    IO_WORD _BGR14 :1;
    IO_WORD _BGR15 :1;
  }bit;
  struct{
    IO_WORD _BGR :16;
  }bitc;
 }BGR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _BGR0 :1;
    IO_BYTE _BGR1 :1;
    IO_BYTE _BGR2 :1;
    IO_BYTE _BGR3 :1;
    IO_BYTE _BGR4 :1;
    IO_BYTE _BGR5 :1;
    IO_BYTE _BGR6 :1;
    IO_BYTE _BGR7 :1;
  }bit;
 }BGRL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _BGR8 :1;
    IO_BYTE _BGR9 :1;
    IO_BYTE _BGR10 :1;
    IO_BYTE _BGR11 :1;
    IO_BYTE _BGR12 :1;
    IO_BYTE _BGR13 :1;
    IO_BYTE _BGR14 :1;
    IO_BYTE _BGR15 :1;
  }bit;
 }BGRH0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _AICD :1;
    IO_BYTE _RBI :1;
    IO_BYTE _RDRF :1;
    IO_BYTE _TDRE :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }ESIR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SOE :1;
    IO_BYTE _SCKE :1;
    IO_BYTE _UPCL :1;
    IO_BYTE _REST :1;
    IO_BYTE _EXT :1;
    IO_BYTE _OTO :1;
    IO_BYTE _MD0 :1;
    IO_BYTE _MD1 :1;
  }bit;
  struct{
    IO_BYTE :6;
    IO_BYTE _MD :2;
  }bitc;
 }SMR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TXE :1;
    IO_BYTE _RXE :1;
    IO_BYTE _CRE :1;
    IO_BYTE _AD :1;
    IO_BYTE _CL :1;
    IO_BYTE _SBL :1;
    IO_BYTE _P :1;
    IO_BYTE _PEN :1;
  }bit;
 }SCR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TIE :1;
    IO_BYTE _RIE :1;
    IO_BYTE _BDS :1;
    IO_BYTE _TDRE :1;
    IO_BYTE _RDRF :1;
    IO_BYTE _FRE :1;
    IO_BYTE _ORE :1;
    IO_BYTE _PE :1;
  }bit;
 }SSR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TBI :1;
    IO_BYTE _RBI :1;
    IO_BYTE _BIE :1;
    IO_BYTE _SSM :1;
    IO_BYTE _SCDE :1;
    IO_BYTE _MS :1;
    IO_BYTE _LBR :1;
    IO_BYTE _INV :1;
  }bit;
 }ECCR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SCES :1;
    IO_BYTE _CCO :1;
    IO_BYTE _SIOP :1;
    IO_BYTE _SOPE :1;
    IO_BYTE _LBL0 :1;
    IO_BYTE _LBL1 :1;
    IO_BYTE _LBD :1;
    IO_BYTE _LBIE :1;
  }bit;
  struct{
    IO_BYTE :4;
    IO_BYTE _LBL :2;
  }bitc;
 }ESCR1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _BGR0 :1;
    IO_WORD _BGR1 :1;
    IO_WORD _BGR2 :1;
    IO_WORD _BGR3 :1;
    IO_WORD _BGR4 :1;
    IO_WORD _BGR5 :1;
    IO_WORD _BGR6 :1;
    IO_WORD _BGR7 :1;
    IO_WORD _BGR8 :1;
    IO_WORD _BGR9 :1;
    IO_WORD _BGR10 :1;
    IO_WORD _BGR11 :1;
    IO_WORD _BGR12 :1;
    IO_WORD _BGR13 :1;
    IO_WORD _BGR14 :1;
    IO_WORD _BGR15 :1;
  }bit;
  struct{
    IO_WORD _BGR :16;
  }bitc;
 }BGR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _BGR0 :1;
    IO_BYTE _BGR1 :1;
    IO_BYTE _BGR2 :1;
    IO_BYTE _BGR3 :1;
    IO_BYTE _BGR4 :1;
    IO_BYTE _BGR5 :1;
    IO_BYTE _BGR6 :1;
    IO_BYTE _BGR7 :1;
  }bit;
 }BGRL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _BGR8 :1;
    IO_BYTE _BGR9 :1;
    IO_BYTE _BGR10 :1;
    IO_BYTE _BGR11 :1;
    IO_BYTE _BGR12 :1;
    IO_BYTE _BGR13 :1;
    IO_BYTE _BGR14 :1;
    IO_BYTE _BGR15 :1;
  }bit;
 }BGRH1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _AICD :1;
    IO_BYTE _RBI :1;
    IO_BYTE _RDRF :1;
    IO_BYTE _TDRE :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }ESIR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SOE :1;
    IO_BYTE _SCKE :1;
    IO_BYTE _UPCL :1;
    IO_BYTE _REST :1;
    IO_BYTE _EXT :1;
    IO_BYTE _OTO :1;
    IO_BYTE _MD0 :1;
    IO_BYTE _MD1 :1;
  }bit;
  struct{
    IO_BYTE :6;
    IO_BYTE _MD :2;
  }bitc;
 }SMR2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TXE :1;
    IO_BYTE _RXE :1;
    IO_BYTE _CRE :1;
    IO_BYTE _AD :1;
    IO_BYTE _CL :1;
    IO_BYTE _SBL :1;
    IO_BYTE _P :1;
    IO_BYTE _PEN :1;
  }bit;
 }SCR2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TIE :1;
    IO_BYTE _RIE :1;
    IO_BYTE _BDS :1;
    IO_BYTE _TDRE :1;
    IO_BYTE _RDRF :1;
    IO_BYTE _FRE :1;
    IO_BYTE _ORE :1;
    IO_BYTE _PE :1;
  }bit;
 }SSR2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TBI :1;
    IO_BYTE _RBI :1;
    IO_BYTE _BIE :1;
    IO_BYTE _SSM :1;
    IO_BYTE _SCDE :1;
    IO_BYTE _MS :1;
    IO_BYTE _LBR :1;
    IO_BYTE _INV :1;
  }bit;
 }ECCR2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SCES :1;
    IO_BYTE _CCO :1;
    IO_BYTE _SIOP :1;
    IO_BYTE _SOPE :1;
    IO_BYTE _LBL0 :1;
    IO_BYTE _LBL1 :1;
    IO_BYTE _LBD :1;
    IO_BYTE _LBIE :1;
  }bit;
  struct{
    IO_BYTE :4;
    IO_BYTE _LBL :2;
  }bitc;
 }ESCR2STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _BGR0 :1;
    IO_WORD _BGR1 :1;
    IO_WORD _BGR2 :1;
    IO_WORD _BGR3 :1;
    IO_WORD _BGR4 :1;
    IO_WORD _BGR5 :1;
    IO_WORD _BGR6 :1;
    IO_WORD _BGR7 :1;
    IO_WORD _BGR8 :1;
    IO_WORD _BGR9 :1;
    IO_WORD _BGR10 :1;
    IO_WORD _BGR11 :1;
    IO_WORD _BGR12 :1;
    IO_WORD _BGR13 :1;
    IO_WORD _BGR14 :1;
    IO_WORD _BGR15 :1;
  }bit;
  struct{
    IO_WORD _BGR :16;
  }bitc;
 }BGR2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _BGR0 :1;
    IO_BYTE _BGR1 :1;
    IO_BYTE _BGR2 :1;
    IO_BYTE _BGR3 :1;
    IO_BYTE _BGR4 :1;
    IO_BYTE _BGR5 :1;
    IO_BYTE _BGR6 :1;
    IO_BYTE _BGR7 :1;
  }bit;
 }BGRL2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _BGR8 :1;
    IO_BYTE _BGR9 :1;
    IO_BYTE _BGR10 :1;
    IO_BYTE _BGR11 :1;
    IO_BYTE _BGR12 :1;
    IO_BYTE _BGR13 :1;
    IO_BYTE _BGR14 :1;
    IO_BYTE _BGR15 :1;
  }bit;
 }BGRH2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _AICD :1;
    IO_BYTE _RBI :1;
    IO_BYTE _RDRF :1;
    IO_BYTE _TDRE :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }ESIR2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SOE :1;
    IO_BYTE _SCKE :1;
    IO_BYTE _UPCL :1;
    IO_BYTE _REST :1;
    IO_BYTE _EXT :1;
    IO_BYTE _OTO :1;
    IO_BYTE _MD0 :1;
    IO_BYTE _MD1 :1;
  }bit;
  struct{
    IO_BYTE :6;
    IO_BYTE _MD :2;
  }bitc;
 }SMR3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TXE :1;
    IO_BYTE _RXE :1;
    IO_BYTE _CRE :1;
    IO_BYTE _AD :1;
    IO_BYTE _CL :1;
    IO_BYTE _SBL :1;
    IO_BYTE _P :1;
    IO_BYTE _PEN :1;
  }bit;
 }SCR3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TIE :1;
    IO_BYTE _RIE :1;
    IO_BYTE _BDS :1;
    IO_BYTE _TDRE :1;
    IO_BYTE _RDRF :1;
    IO_BYTE _FRE :1;
    IO_BYTE _ORE :1;
    IO_BYTE _PE :1;
  }bit;
 }SSR3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TBI :1;
    IO_BYTE _RBI :1;
    IO_BYTE _BIE :1;
    IO_BYTE _SSM :1;
    IO_BYTE _SCDE :1;
    IO_BYTE _MS :1;
    IO_BYTE _LBR :1;
    IO_BYTE _INV :1;
  }bit;
 }ECCR3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SCES :1;
    IO_BYTE _CCO :1;
    IO_BYTE _SIOP :1;
    IO_BYTE _SOPE :1;
    IO_BYTE _LBL0 :1;
    IO_BYTE _LBL1 :1;
    IO_BYTE _LBD :1;
    IO_BYTE _LBIE :1;
  }bit;
  struct{
    IO_BYTE :4;
    IO_BYTE _LBL :2;
  }bitc;
 }ESCR3STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _BGR0 :1;
    IO_WORD _BGR1 :1;
    IO_WORD _BGR2 :1;
    IO_WORD _BGR3 :1;
    IO_WORD _BGR4 :1;
    IO_WORD _BGR5 :1;
    IO_WORD _BGR6 :1;
    IO_WORD _BGR7 :1;
    IO_WORD _BGR8 :1;
    IO_WORD _BGR9 :1;
    IO_WORD _BGR10 :1;
    IO_WORD _BGR11 :1;
    IO_WORD _BGR12 :1;
    IO_WORD _BGR13 :1;
    IO_WORD _BGR14 :1;
    IO_WORD _BGR15 :1;
  }bit;
  struct{
    IO_WORD _BGR :16;
  }bitc;
 }BGR3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _BGR0 :1;
    IO_BYTE _BGR1 :1;
    IO_BYTE _BGR2 :1;
    IO_BYTE _BGR3 :1;
    IO_BYTE _BGR4 :1;
    IO_BYTE _BGR5 :1;
    IO_BYTE _BGR6 :1;
    IO_BYTE _BGR7 :1;
  }bit;
 }BGRL3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _BGR8 :1;
    IO_BYTE _BGR9 :1;
    IO_BYTE _BGR10 :1;
    IO_BYTE _BGR11 :1;
    IO_BYTE _BGR12 :1;
    IO_BYTE _BGR13 :1;
    IO_BYTE _BGR14 :1;
    IO_BYTE _BGR15 :1;
  }bit;
 }BGRH3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _AICD :1;
    IO_BYTE _RBI :1;
    IO_BYTE _RDRF :1;
    IO_BYTE _TDRE :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }ESIR3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SE :1;
    IO_BYTE _DIR :1;
    IO_BYTE _BF :1;
    IO_BYTE _BW :1;
    IO_BYTE _IF :1;
    IO_BYTE _BPD :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }DMACS0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SE :1;
    IO_BYTE _DIR :1;
    IO_BYTE _BF :1;
    IO_BYTE _BW :1;
    IO_BYTE _IF :1;
    IO_BYTE _BPD :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }DMACS1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SE :1;
    IO_BYTE _DIR :1;
    IO_BYTE _BF :1;
    IO_BYTE _BW :1;
    IO_BYTE _IF :1;
    IO_BYTE _BPD :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }DMACS2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SE :1;
    IO_BYTE _DIR :1;
    IO_BYTE _BF :1;
    IO_BYTE _BW :1;
    IO_BYTE _IF :1;
    IO_BYTE _BPD :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }DMACS3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SE :1;
    IO_BYTE _DIR :1;
    IO_BYTE _BF :1;
    IO_BYTE _BW :1;
    IO_BYTE _IF :1;
    IO_BYTE _BPD :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }DMACS4STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SE :1;
    IO_BYTE _DIR :1;
    IO_BYTE _BF :1;
    IO_BYTE _BW :1;
    IO_BYTE _IF :1;
    IO_BYTE _BPD :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }DMACS5STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _DTE0 :1;
    IO_WORD _DTE1 :1;
    IO_WORD _DTE2 :1;
    IO_WORD _DTE3 :1;
    IO_WORD _DTE4 :1;
    IO_WORD _DTE5 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }DSRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _DTE0 :1;
    IO_BYTE _DTE1 :1;
    IO_BYTE _DTE2 :1;
    IO_BYTE _DTE3 :1;
    IO_BYTE _DTE4 :1;
    IO_BYTE _DTE5 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }DSRLSTR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _STP0 :1;
    IO_WORD _STP1 :1;
    IO_WORD _STP2 :1;
    IO_WORD _STP3 :1;
    IO_WORD _STP4 :1;
    IO_WORD _STP5 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }DSSRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _STP0 :1;
    IO_BYTE _STP1 :1;
    IO_BYTE _STP2 :1;
    IO_BYTE _STP3 :1;
    IO_BYTE _STP4 :1;
    IO_BYTE _STP5 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }DSSRLSTR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _EN0 :1;
    IO_WORD _EN1 :1;
    IO_WORD _EN2 :1;
    IO_WORD _EN3 :1;
    IO_WORD _EN4 :1;
    IO_WORD _EN5 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }DERSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EN0 :1;
    IO_BYTE _EN1 :1;
    IO_BYTE _EN2 :1;
    IO_BYTE _EN3 :1;
    IO_BYTE _EN4 :1;
    IO_BYTE _EN5 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }DERLSTR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _IL0 :1;
    IO_WORD _IL1 :1;
    IO_WORD _IL2 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _IX0 :1;
    IO_WORD _IX1 :1;
    IO_WORD _IX2 :1;
    IO_WORD _IX3 :1;
    IO_WORD _IX4 :1;
    IO_WORD _IX5 :1;
    IO_WORD _IX6 :1;
    IO_WORD _IX7 :1;
  }bit;
  struct{
    IO_WORD _IL :3;
    IO_WORD :5;
    IO_WORD _IX :8;
  }bitc;
 }ICRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IL0 :1;
    IO_BYTE _IL1 :1;
    IO_BYTE _IL2 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _IL :3;
  }bitc;
 }ILRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IX0 :1;
    IO_BYTE _IX1 :1;
    IO_BYTE _IX2 :1;
    IO_BYTE _IX3 :1;
    IO_BYTE _IX4 :1;
    IO_BYTE _IX5 :1;
    IO_BYTE _IX6 :1;
    IO_BYTE _IX7 :1;
  }bit;
  struct{
    IO_BYTE _IX :8;
  }bitc;
 }IDXSTR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _TB10 :1;
    IO_WORD _TB11 :1;
    IO_WORD _TB12 :1;
    IO_WORD _TB13 :1;
    IO_WORD _TB14 :1;
    IO_WORD _TB15 :1;
    IO_WORD _TB16 :1;
    IO_WORD _TB17 :1;
    IO_WORD _TB18 :1;
    IO_WORD _TB19 :1;
    IO_WORD _TB20 :1;
    IO_WORD _TB21 :1;
    IO_WORD _TB22 :1;
    IO_WORD _TB23 :1;
  }bit;
 }TBRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _TB10 :1;
    IO_BYTE _TB11 :1;
    IO_BYTE _TB12 :1;
    IO_BYTE _TB13 :1;
    IO_BYTE _TB14 :1;
    IO_BYTE _TB15 :1;
  }bit;
 }TBRLSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TB16 :1;
    IO_BYTE _TB17 :1;
    IO_BYTE _TB18 :1;
    IO_BYTE _TB19 :1;
    IO_BYTE _TB20 :1;
    IO_BYTE _TB21 :1;
    IO_BYTE _TB22 :1;
    IO_BYTE _TB23 :1;
  }bit;
 }TBRHSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _R0 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }DIRRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _FLAG :1;
    IO_BYTE _EN :1;
    IO_BYTE _LEV :1;
    IO_BYTE _INT9FIX :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }NMISTR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _RSEL0 :1;
    IO_WORD _RSEL1 :1;
    IO_WORD _RSEL2 :1;
    IO_WORD _RSEL3 :1;
    IO_WORD _RSEL4 :1;
    IO_WORD _RSEL5 :1;
    IO_WORD _RSEL6 :1;
    IO_WORD _RSEL7 :1;
    IO_WORD _TSEL0 :1;
    IO_WORD _TSEL1 :1;
    IO_WORD _TSEL2 :1;
    IO_WORD _TSEL3 :1;
    IO_WORD _TSEL4 :1;
    IO_WORD _TSEL5 :1;
    IO_WORD _TSEL6 :1;
    IO_WORD _TSEL7 :1;
  }bit;
  struct{
    IO_WORD _RSEL :8;
    IO_WORD _TSEL :8;
  }bitc;
 }EDSU2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MI :1;
    IO_BYTE _SZ0 :1;
    IO_BYTE _SZ1 :1;
    IO_BYTE  :1;
    IO_BYTE _BS0 :1;
    IO_BYTE _BS1 :1;
    IO_BYTE _BS2 :1;
    IO_BYTE _BS3 :1;
  }bit;
 }ROMMSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _RINT :1;
    IO_BYTE _RIE :1;
    IO_BYTE _SEL0 :1;
    IO_BYTE _SEL1 :1;
    IO_BYTE _TINT :1;
    IO_BYTE _TIE :1;
    IO_BYTE  :1;
    IO_BYTE _EN :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _SEL :2;
  }bitc;
 }EDSUSTR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _I0 :1;
    IO_WORD _I1 :1;
    IO_WORD _IE0 :1;
    IO_WORD _IE1 :1;
    IO_WORD _PE0 :1;
    IO_WORD _PE1 :1;
    IO_WORD _AR :1;
    IO_WORD _AM :1;
    IO_WORD _DMA :1;
    IO_WORD _CPU :1;
    IO_WORD _DATA :1;
    IO_WORD _CODE :1;
    IO_WORD _WORD :1;
    IO_WORD _BYTE :1;
    IO_WORD _WRITE :1;
    IO_WORD _READ :1;
  }bit;
 }PFCS0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _I0 :1;
    IO_WORD _I1 :1;
    IO_WORD _IE0 :1;
    IO_WORD _IE1 :1;
    IO_WORD _PE0 :1;
    IO_WORD _PE1 :1;
    IO_WORD _AR :1;
    IO_WORD _AM :1;
    IO_WORD _DMA :1;
    IO_WORD _CPU :1;
    IO_WORD _DATA :1;
    IO_WORD _CODE :1;
    IO_WORD _WORD :1;
    IO_WORD _BYTE :1;
    IO_WORD _WRITE :1;
    IO_WORD _READ :1;
  }bit;
 }PFCS1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _I0 :1;
    IO_WORD _I1 :1;
    IO_WORD _IE0 :1;
    IO_WORD _IE1 :1;
    IO_WORD _PE0 :1;
    IO_WORD _PE1 :1;
    IO_WORD _AR :1;
    IO_WORD _AM :1;
    IO_WORD _DMA :1;
    IO_WORD _CPU :1;
    IO_WORD _DATA :1;
    IO_WORD _CODE :1;
    IO_WORD _WORD :1;
    IO_WORD _BYTE :1;
    IO_WORD _WRITE :1;
    IO_WORD _READ :1;
  }bit;
 }PFCS2STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _I0 :1;
    IO_WORD _I1 :1;
    IO_WORD _IE0 :1;
    IO_WORD _IE1 :1;
    IO_WORD _PE0 :1;
    IO_WORD _PE1 :1;
    IO_WORD _AR :1;
    IO_WORD _AM :1;
    IO_WORD _DMA :1;
    IO_WORD _CPU :1;
    IO_WORD _DATA :1;
    IO_WORD _CODE :1;
    IO_WORD _WORD :1;
    IO_WORD _BYTE :1;
    IO_WORD _WRITE :1;
    IO_WORD _READ :1;
  }bit;
 }PFCS3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA0 :1;
    IO_BYTE _PFA1 :1;
    IO_BYTE _PFA2 :1;
    IO_BYTE _PFA3 :1;
    IO_BYTE _PFA4 :1;
    IO_BYTE _PFA5 :1;
    IO_BYTE _PFA6 :1;
    IO_BYTE _PFA7 :1;
  }bit;
 }PFAL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA8 :1;
    IO_BYTE _PFA9 :1;
    IO_BYTE _PFA10 :1;
    IO_BYTE _PFA11 :1;
    IO_BYTE _PFA12 :1;
    IO_BYTE _PFA13 :1;
    IO_BYTE _PFA14 :1;
    IO_BYTE _PFA15 :1;
  }bit;
 }PFAM0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA16 :1;
    IO_BYTE _PFA17 :1;
    IO_BYTE _PFA18 :1;
    IO_BYTE _PFA19 :1;
    IO_BYTE _PFA20 :1;
    IO_BYTE _PFA21 :1;
    IO_BYTE _PFA22 :1;
    IO_BYTE _PFA23 :1;
  }bit;
 }PFAH0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA0 :1;
    IO_BYTE _PFA1 :1;
    IO_BYTE _PFA2 :1;
    IO_BYTE _PFA3 :1;
    IO_BYTE _PFA4 :1;
    IO_BYTE _PFA5 :1;
    IO_BYTE _PFA6 :1;
    IO_BYTE _PFA7 :1;
  }bit;
 }PFAL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA8 :1;
    IO_BYTE _PFA9 :1;
    IO_BYTE _PFA10 :1;
    IO_BYTE _PFA11 :1;
    IO_BYTE _PFA12 :1;
    IO_BYTE _PFA13 :1;
    IO_BYTE _PFA14 :1;
    IO_BYTE _PFA15 :1;
  }bit;
 }PFAM1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA16 :1;
    IO_BYTE _PFA17 :1;
    IO_BYTE _PFA18 :1;
    IO_BYTE _PFA19 :1;
    IO_BYTE _PFA20 :1;
    IO_BYTE _PFA21 :1;
    IO_BYTE _PFA22 :1;
    IO_BYTE _PFA23 :1;
  }bit;
 }PFAH1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA0 :1;
    IO_BYTE _PFA1 :1;
    IO_BYTE _PFA2 :1;
    IO_BYTE _PFA3 :1;
    IO_BYTE _PFA4 :1;
    IO_BYTE _PFA5 :1;
    IO_BYTE _PFA6 :1;
    IO_BYTE _PFA7 :1;
  }bit;
 }PFAL2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA8 :1;
    IO_BYTE _PFA9 :1;
    IO_BYTE _PFA10 :1;
    IO_BYTE _PFA11 :1;
    IO_BYTE _PFA12 :1;
    IO_BYTE _PFA13 :1;
    IO_BYTE _PFA14 :1;
    IO_BYTE _PFA15 :1;
  }bit;
 }PFAM2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA16 :1;
    IO_BYTE _PFA17 :1;
    IO_BYTE _PFA18 :1;
    IO_BYTE _PFA19 :1;
    IO_BYTE _PFA20 :1;
    IO_BYTE _PFA21 :1;
    IO_BYTE _PFA22 :1;
    IO_BYTE _PFA23 :1;
  }bit;
 }PFAH2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA0 :1;
    IO_BYTE _PFA1 :1;
    IO_BYTE _PFA2 :1;
    IO_BYTE _PFA3 :1;
    IO_BYTE _PFA4 :1;
    IO_BYTE _PFA5 :1;
    IO_BYTE _PFA6 :1;
    IO_BYTE _PFA7 :1;
  }bit;
 }PFAL3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA8 :1;
    IO_BYTE _PFA9 :1;
    IO_BYTE _PFA10 :1;
    IO_BYTE _PFA11 :1;
    IO_BYTE _PFA12 :1;
    IO_BYTE _PFA13 :1;
    IO_BYTE _PFA14 :1;
    IO_BYTE _PFA15 :1;
  }bit;
 }PFAM3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA16 :1;
    IO_BYTE _PFA17 :1;
    IO_BYTE _PFA18 :1;
    IO_BYTE _PFA19 :1;
    IO_BYTE _PFA20 :1;
    IO_BYTE _PFA21 :1;
    IO_BYTE _PFA22 :1;
    IO_BYTE _PFA23 :1;
  }bit;
 }PFAH3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA0 :1;
    IO_BYTE _PFA1 :1;
    IO_BYTE _PFA2 :1;
    IO_BYTE _PFA3 :1;
    IO_BYTE _PFA4 :1;
    IO_BYTE _PFA5 :1;
    IO_BYTE _PFA6 :1;
    IO_BYTE _PFA7 :1;
  }bit;
 }PFAL4STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA8 :1;
    IO_BYTE _PFA9 :1;
    IO_BYTE _PFA10 :1;
    IO_BYTE _PFA11 :1;
    IO_BYTE _PFA12 :1;
    IO_BYTE _PFA13 :1;
    IO_BYTE _PFA14 :1;
    IO_BYTE _PFA15 :1;
  }bit;
 }PFAM4STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA16 :1;
    IO_BYTE _PFA17 :1;
    IO_BYTE _PFA18 :1;
    IO_BYTE _PFA19 :1;
    IO_BYTE _PFA20 :1;
    IO_BYTE _PFA21 :1;
    IO_BYTE _PFA22 :1;
    IO_BYTE _PFA23 :1;
  }bit;
 }PFAH4STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA0 :1;
    IO_BYTE _PFA1 :1;
    IO_BYTE _PFA2 :1;
    IO_BYTE _PFA3 :1;
    IO_BYTE _PFA4 :1;
    IO_BYTE _PFA5 :1;
    IO_BYTE _PFA6 :1;
    IO_BYTE _PFA7 :1;
  }bit;
 }PFAL5STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA8 :1;
    IO_BYTE _PFA9 :1;
    IO_BYTE _PFA10 :1;
    IO_BYTE _PFA11 :1;
    IO_BYTE _PFA12 :1;
    IO_BYTE _PFA13 :1;
    IO_BYTE _PFA14 :1;
    IO_BYTE _PFA15 :1;
  }bit;
 }PFAM5STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA16 :1;
    IO_BYTE _PFA17 :1;
    IO_BYTE _PFA18 :1;
    IO_BYTE _PFA19 :1;
    IO_BYTE _PFA20 :1;
    IO_BYTE _PFA21 :1;
    IO_BYTE _PFA22 :1;
    IO_BYTE _PFA23 :1;
  }bit;
 }PFAH5STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA0 :1;
    IO_BYTE _PFA1 :1;
    IO_BYTE _PFA2 :1;
    IO_BYTE _PFA3 :1;
    IO_BYTE _PFA4 :1;
    IO_BYTE _PFA5 :1;
    IO_BYTE _PFA6 :1;
    IO_BYTE _PFA7 :1;
  }bit;
 }PFAL6STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA8 :1;
    IO_BYTE _PFA9 :1;
    IO_BYTE _PFA10 :1;
    IO_BYTE _PFA11 :1;
    IO_BYTE _PFA12 :1;
    IO_BYTE _PFA13 :1;
    IO_BYTE _PFA14 :1;
    IO_BYTE _PFA15 :1;
  }bit;
 }PFAM6STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA16 :1;
    IO_BYTE _PFA17 :1;
    IO_BYTE _PFA18 :1;
    IO_BYTE _PFA19 :1;
    IO_BYTE _PFA20 :1;
    IO_BYTE _PFA21 :1;
    IO_BYTE _PFA22 :1;
    IO_BYTE _PFA23 :1;
  }bit;
 }PFAH6STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA0 :1;
    IO_BYTE _PFA1 :1;
    IO_BYTE _PFA2 :1;
    IO_BYTE _PFA3 :1;
    IO_BYTE _PFA4 :1;
    IO_BYTE _PFA5 :1;
    IO_BYTE _PFA6 :1;
    IO_BYTE _PFA7 :1;
  }bit;
 }PFAL7STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA8 :1;
    IO_BYTE _PFA9 :1;
    IO_BYTE _PFA10 :1;
    IO_BYTE _PFA11 :1;
    IO_BYTE _PFA12 :1;
    IO_BYTE _PFA13 :1;
    IO_BYTE _PFA14 :1;
    IO_BYTE _PFA15 :1;
  }bit;
 }PFAM7STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFA16 :1;
    IO_BYTE _PFA17 :1;
    IO_BYTE _PFA18 :1;
    IO_BYTE _PFA19 :1;
    IO_BYTE _PFA20 :1;
    IO_BYTE _PFA21 :1;
    IO_BYTE _PFA22 :1;
    IO_BYTE _PFA23 :1;
  }bit;
 }PFAH7STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _PFD0 :1;
    IO_WORD _PFD1 :1;
    IO_WORD _PFD2 :1;
    IO_WORD _PFD3 :1;
    IO_WORD _PFD4 :1;
    IO_WORD _PFD5 :1;
    IO_WORD _PFD6 :1;
    IO_WORD _PFD7 :1;
    IO_WORD _PFD8 :1;
    IO_WORD _PFD9 :1;
    IO_WORD _PFD10 :1;
    IO_WORD _PFD11 :1;
    IO_WORD _PFD12 :1;
    IO_WORD _PFD13 :1;
    IO_WORD _PFD14 :1;
    IO_WORD _PFD15 :1;
  }bit;
  struct{
    IO_WORD _PFD :16;
  }bitc;
 }PFD0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFD0 :1;
    IO_BYTE _PFD1 :1;
    IO_BYTE _PFD2 :1;
    IO_BYTE _PFD3 :1;
    IO_BYTE _PFD4 :1;
    IO_BYTE _PFD5 :1;
    IO_BYTE _PFD6 :1;
    IO_BYTE _PFD7 :1;
  }bit;
 }PFDL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFD8 :1;
    IO_BYTE _PFD9 :1;
    IO_BYTE _PFD10 :1;
    IO_BYTE _PFD11 :1;
    IO_BYTE _PFD12 :1;
    IO_BYTE _PFD13 :1;
    IO_BYTE _PFD14 :1;
    IO_BYTE _PFD15 :1;
  }bit;
 }PFDH0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _PFD0 :1;
    IO_WORD _PFD1 :1;
    IO_WORD _PFD2 :1;
    IO_WORD _PFD3 :1;
    IO_WORD _PFD4 :1;
    IO_WORD _PFD5 :1;
    IO_WORD _PFD6 :1;
    IO_WORD _PFD7 :1;
    IO_WORD _PFD8 :1;
    IO_WORD _PFD9 :1;
    IO_WORD _PFD10 :1;
    IO_WORD _PFD11 :1;
    IO_WORD _PFD12 :1;
    IO_WORD _PFD13 :1;
    IO_WORD _PFD14 :1;
    IO_WORD _PFD15 :1;
  }bit;
  struct{
    IO_WORD _PFD :16;
  }bitc;
 }PFD1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFD0 :1;
    IO_BYTE _PFD1 :1;
    IO_BYTE _PFD2 :1;
    IO_BYTE _PFD3 :1;
    IO_BYTE _PFD4 :1;
    IO_BYTE _PFD5 :1;
    IO_BYTE _PFD6 :1;
    IO_BYTE _PFD7 :1;
  }bit;
 }PFDL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFD8 :1;
    IO_BYTE _PFD9 :1;
    IO_BYTE _PFD10 :1;
    IO_BYTE _PFD11 :1;
    IO_BYTE _PFD12 :1;
    IO_BYTE _PFD13 :1;
    IO_BYTE _PFD14 :1;
    IO_BYTE _PFD15 :1;
  }bit;
 }PFDH1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _PFD0 :1;
    IO_WORD _PFD1 :1;
    IO_WORD _PFD2 :1;
    IO_WORD _PFD3 :1;
    IO_WORD _PFD4 :1;
    IO_WORD _PFD5 :1;
    IO_WORD _PFD6 :1;
    IO_WORD _PFD7 :1;
    IO_WORD _PFD8 :1;
    IO_WORD _PFD9 :1;
    IO_WORD _PFD10 :1;
    IO_WORD _PFD11 :1;
    IO_WORD _PFD12 :1;
    IO_WORD _PFD13 :1;
    IO_WORD _PFD14 :1;
    IO_WORD _PFD15 :1;
  }bit;
  struct{
    IO_WORD _PFD :16;
  }bitc;
 }PFD2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFD0 :1;
    IO_BYTE _PFD1 :1;
    IO_BYTE _PFD2 :1;
    IO_BYTE _PFD3 :1;
    IO_BYTE _PFD4 :1;
    IO_BYTE _PFD5 :1;
    IO_BYTE _PFD6 :1;
    IO_BYTE _PFD7 :1;
  }bit;
 }PFDL2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFD8 :1;
    IO_BYTE _PFD9 :1;
    IO_BYTE _PFD10 :1;
    IO_BYTE _PFD11 :1;
    IO_BYTE _PFD12 :1;
    IO_BYTE _PFD13 :1;
    IO_BYTE _PFD14 :1;
    IO_BYTE _PFD15 :1;
  }bit;
 }PFDH2STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _PFD0 :1;
    IO_WORD _PFD1 :1;
    IO_WORD _PFD2 :1;
    IO_WORD _PFD3 :1;
    IO_WORD _PFD4 :1;
    IO_WORD _PFD5 :1;
    IO_WORD _PFD6 :1;
    IO_WORD _PFD7 :1;
    IO_WORD _PFD8 :1;
    IO_WORD _PFD9 :1;
    IO_WORD _PFD10 :1;
    IO_WORD _PFD11 :1;
    IO_WORD _PFD12 :1;
    IO_WORD _PFD13 :1;
    IO_WORD _PFD14 :1;
    IO_WORD _PFD15 :1;
  }bit;
  struct{
    IO_WORD _PFD :16;
  }bitc;
 }PFD3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFD0 :1;
    IO_BYTE _PFD1 :1;
    IO_BYTE _PFD2 :1;
    IO_BYTE _PFD3 :1;
    IO_BYTE _PFD4 :1;
    IO_BYTE _PFD5 :1;
    IO_BYTE _PFD6 :1;
    IO_BYTE _PFD7 :1;
  }bit;
 }PFDL3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFD8 :1;
    IO_BYTE _PFD9 :1;
    IO_BYTE _PFD10 :1;
    IO_BYTE _PFD11 :1;
    IO_BYTE _PFD12 :1;
    IO_BYTE _PFD13 :1;
    IO_BYTE _PFD14 :1;
    IO_BYTE _PFD15 :1;
  }bit;
 }PFDH3STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _PFD0 :1;
    IO_WORD _PFD1 :1;
    IO_WORD _PFD2 :1;
    IO_WORD _PFD3 :1;
    IO_WORD _PFD4 :1;
    IO_WORD _PFD5 :1;
    IO_WORD _PFD6 :1;
    IO_WORD _PFD7 :1;
    IO_WORD _PFD8 :1;
    IO_WORD _PFD9 :1;
    IO_WORD _PFD10 :1;
    IO_WORD _PFD11 :1;
    IO_WORD _PFD12 :1;
    IO_WORD _PFD13 :1;
    IO_WORD _PFD14 :1;
    IO_WORD _PFD15 :1;
  }bit;
  struct{
    IO_WORD _PFD :16;
  }bitc;
 }PFD4STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFD0 :1;
    IO_BYTE _PFD1 :1;
    IO_BYTE _PFD2 :1;
    IO_BYTE _PFD3 :1;
    IO_BYTE _PFD4 :1;
    IO_BYTE _PFD5 :1;
    IO_BYTE _PFD6 :1;
    IO_BYTE _PFD7 :1;
  }bit;
 }PFDL4STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFD8 :1;
    IO_BYTE _PFD9 :1;
    IO_BYTE _PFD10 :1;
    IO_BYTE _PFD11 :1;
    IO_BYTE _PFD12 :1;
    IO_BYTE _PFD13 :1;
    IO_BYTE _PFD14 :1;
    IO_BYTE _PFD15 :1;
  }bit;
 }PFDH4STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _PFD0 :1;
    IO_WORD _PFD1 :1;
    IO_WORD _PFD2 :1;
    IO_WORD _PFD3 :1;
    IO_WORD _PFD4 :1;
    IO_WORD _PFD5 :1;
    IO_WORD _PFD6 :1;
    IO_WORD _PFD7 :1;
    IO_WORD _PFD8 :1;
    IO_WORD _PFD9 :1;
    IO_WORD _PFD10 :1;
    IO_WORD _PFD11 :1;
    IO_WORD _PFD12 :1;
    IO_WORD _PFD13 :1;
    IO_WORD _PFD14 :1;
    IO_WORD _PFD15 :1;
  }bit;
  struct{
    IO_WORD _PFD :16;
  }bitc;
 }PFD5STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFD0 :1;
    IO_BYTE _PFD1 :1;
    IO_BYTE _PFD2 :1;
    IO_BYTE _PFD3 :1;
    IO_BYTE _PFD4 :1;
    IO_BYTE _PFD5 :1;
    IO_BYTE _PFD6 :1;
    IO_BYTE _PFD7 :1;
  }bit;
 }PFDL5STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFD8 :1;
    IO_BYTE _PFD9 :1;
    IO_BYTE _PFD10 :1;
    IO_BYTE _PFD11 :1;
    IO_BYTE _PFD12 :1;
    IO_BYTE _PFD13 :1;
    IO_BYTE _PFD14 :1;
    IO_BYTE _PFD15 :1;
  }bit;
 }PFDH5STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _PFD0 :1;
    IO_WORD _PFD1 :1;
    IO_WORD _PFD2 :1;
    IO_WORD _PFD3 :1;
    IO_WORD _PFD4 :1;
    IO_WORD _PFD5 :1;
    IO_WORD _PFD6 :1;
    IO_WORD _PFD7 :1;
    IO_WORD _PFD8 :1;
    IO_WORD _PFD9 :1;
    IO_WORD _PFD10 :1;
    IO_WORD _PFD11 :1;
    IO_WORD _PFD12 :1;
    IO_WORD _PFD13 :1;
    IO_WORD _PFD14 :1;
    IO_WORD _PFD15 :1;
  }bit;
  struct{
    IO_WORD _PFD :16;
  }bitc;
 }PFD6STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFD0 :1;
    IO_BYTE _PFD1 :1;
    IO_BYTE _PFD2 :1;
    IO_BYTE _PFD3 :1;
    IO_BYTE _PFD4 :1;
    IO_BYTE _PFD5 :1;
    IO_BYTE _PFD6 :1;
    IO_BYTE _PFD7 :1;
  }bit;
 }PFDL6STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFD8 :1;
    IO_BYTE _PFD9 :1;
    IO_BYTE _PFD10 :1;
    IO_BYTE _PFD11 :1;
    IO_BYTE _PFD12 :1;
    IO_BYTE _PFD13 :1;
    IO_BYTE _PFD14 :1;
    IO_BYTE _PFD15 :1;
  }bit;
 }PFDH6STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _PFD0 :1;
    IO_WORD _PFD1 :1;
    IO_WORD _PFD2 :1;
    IO_WORD _PFD3 :1;
    IO_WORD _PFD4 :1;
    IO_WORD _PFD5 :1;
    IO_WORD _PFD6 :1;
    IO_WORD _PFD7 :1;
    IO_WORD _PFD8 :1;
    IO_WORD _PFD9 :1;
    IO_WORD _PFD10 :1;
    IO_WORD _PFD11 :1;
    IO_WORD _PFD12 :1;
    IO_WORD _PFD13 :1;
    IO_WORD _PFD14 :1;
    IO_WORD _PFD15 :1;
  }bit;
  struct{
    IO_WORD _PFD :16;
  }bitc;
 }PFD7STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFD0 :1;
    IO_BYTE _PFD1 :1;
    IO_BYTE _PFD2 :1;
    IO_BYTE _PFD3 :1;
    IO_BYTE _PFD4 :1;
    IO_BYTE _PFD5 :1;
    IO_BYTE _PFD6 :1;
    IO_BYTE _PFD7 :1;
  }bit;
 }PFDL7STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PFD8 :1;
    IO_BYTE _PFD9 :1;
    IO_BYTE _PFD10 :1;
    IO_BYTE _PFD11 :1;
    IO_BYTE _PFD12 :1;
    IO_BYTE _PFD13 :1;
    IO_BYTE _PFD14 :1;
    IO_BYTE _PFD15 :1;
  }bit;
 }PFDH7STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _RDY :1;
    IO_BYTE _RDYINT :1;
    IO_BYTE _INTE :1;
    IO_BYTE _WE :1;
    IO_BYTE _CRBE :1;
    IO_BYTE _DRBE :1;
    IO_BYTE _RD19V :1;
    IO_BYTE  :1;
  }bit;
 }MFMCSSTR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _FAWC0 :1;
    IO_WORD _FAWC1 :1;
    IO_WORD _FAWC2 :1;
    IO_WORD _SYNC :1;
    IO_WORD _ADS :1;
    IO_WORD _CLKBW :1;
    IO_WORD _WEXL :1;
    IO_WORD  :1;
    IO_WORD _ATDINIT :1;
    IO_WORD _ATDL0 :1;
    IO_WORD _ATDL1 :1;
    IO_WORD _ATDEQD0 :1;
    IO_WORD _ATDEQD1 :1;
    IO_WORD _EQL0 :1;
    IO_WORD _EQL1 :1;
    IO_WORD _EQL2 :1;
  }bit;
  struct{
    IO_WORD _FAWC :3;
    IO_WORD :6;
    IO_WORD _ATDL :2;
    IO_WORD _ATDEQD :2;
    IO_WORD _EQL :3;
  }bitc;
 }MFMTCSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _FAWC0 :1;
    IO_BYTE _FAWC1 :1;
    IO_BYTE _FAWC2 :1;
    IO_BYTE _SYNC :1;
    IO_BYTE _ADS :1;
    IO_BYTE _CLKBW :1;
    IO_BYTE _WEXL :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _FAWC :3;
  }bitc;
 }MFMTCLSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ATDINIT :1;
    IO_BYTE _ATDL0 :1;
    IO_BYTE _ATDL1 :1;
    IO_BYTE _ATDEQD0 :1;
    IO_BYTE _ATDEQD1 :1;
    IO_BYTE _EQL0 :1;
    IO_BYTE _EQL1 :1;
    IO_BYTE _EQL2 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE _ATDL :2;
    IO_BYTE _ATDEQD :2;
    IO_BYTE _EQL :3;
  }bitc;
 }MFMTCHSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _RDY :1;
    IO_BYTE _RDYINT :1;
    IO_BYTE _INTE :1;
    IO_BYTE _WE :1;
    IO_BYTE _CRBE :1;
    IO_BYTE _DRBE :1;
    IO_BYTE _RD19V :1;
    IO_BYTE  :1;
  }bit;
 }SFMCSSTR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _FAWC0 :1;
    IO_WORD _FAWC1 :1;
    IO_WORD _FAWC2 :1;
    IO_WORD _SYNC :1;
    IO_WORD _ADS :1;
    IO_WORD _CLKBW :1;
    IO_WORD _WEXL :1;
    IO_WORD  :1;
    IO_WORD _ATDINIT :1;
    IO_WORD _ATDL0 :1;
    IO_WORD _ATDL1 :1;
    IO_WORD _ATDEQD0 :1;
    IO_WORD _ATDEQD1 :1;
    IO_WORD _EQL0 :1;
    IO_WORD _EQL1 :1;
    IO_WORD _EQL2 :1;
  }bit;
  struct{
    IO_WORD _FAWC :3;
    IO_WORD :6;
    IO_WORD _ATDL :2;
    IO_WORD _ATDEQD :2;
    IO_WORD _EQL :3;
  }bitc;
 }SFMTCSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _FAWC0 :1;
    IO_BYTE _FAWC1 :1;
    IO_BYTE _FAWC2 :1;
    IO_BYTE _SYNC :1;
    IO_BYTE _ADS :1;
    IO_BYTE _CLKBW :1;
    IO_BYTE _WEXL :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _FAWC :3;
  }bitc;
 }SFMTCLSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ATDINIT :1;
    IO_BYTE _ATDL0 :1;
    IO_BYTE _ATDL1 :1;
    IO_BYTE _ATDEQD0 :1;
    IO_BYTE _ATDEQD1 :1;
    IO_BYTE _EQL0 :1;
    IO_BYTE _EQL1 :1;
    IO_BYTE _EQL2 :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE _ATDL :2;
    IO_BYTE _ATDEQD :2;
    IO_BYTE _EQL :3;
  }bitc;
 }SFMTCHSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _WCB0 :1;
    IO_BYTE _WCB1 :1;
    IO_BYTE _WCB2 :1;
    IO_BYTE _WCB3 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _WCB :4;
  }bitc;
 }FMWC0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _WCA0 :1;
    IO_BYTE _WCA1 :1;
    IO_BYTE _WCA2 :1;
    IO_BYTE _WCA3 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _WCA :4;
  }bitc;
 }FMWC1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _WC32 :1;
    IO_BYTE _WC33 :1;
    IO_BYTE _WC34 :1;
    IO_BYTE _WC35 :1;
    IO_BYTE _WC36 :1;
    IO_BYTE _WC37 :1;
    IO_BYTE _WC38 :1;
    IO_BYTE _WC39 :1;
  }bit;
  struct{
    IO_BYTE _WC3 :8;
  }bitc;
 }FMWC5STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SMS0 :1;
    IO_BYTE _SMS1 :1;
    IO_BYTE _SPL :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _SMS :2;
  }bitc;
 }SMCRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SC1S0 :1;
    IO_BYTE _SC1S1 :1;
    IO_BYTE _SC2S0 :1;
    IO_BYTE _SC2S1 :1;
    IO_BYTE _RCE :1;
    IO_BYTE _MCE :1;
    IO_BYTE _PCE :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _SC1S :2;
    IO_BYTE _SC2S :2;
  }bitc;
 }CKSRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MCST0 :1;
    IO_BYTE _MCST1 :1;
    IO_BYTE _MCST2 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _PCST :1;
    IO_BYTE _MRFBE :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _MCST :3;
  }bitc;
 }CKSSRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SC1M0 :1;
    IO_BYTE _SC1M1 :1;
    IO_BYTE _SC2M0 :1;
    IO_BYTE _SC2M1 :1;
    IO_BYTE _RCM :1;
    IO_BYTE _MCM :1;
    IO_BYTE _PCM :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _SC1M :2;
    IO_BYTE _SC2M :2;
  }bitc;
 }CKMRSTR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _RCFS :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _BCD0 :1;
    IO_WORD _BCD1 :1;
    IO_WORD _BCD2 :1;
    IO_WORD _BCD3 :1;
    IO_WORD _PC1D0 :1;
    IO_WORD _PC1D1 :1;
    IO_WORD _PC1D2 :1;
    IO_WORD _PC1D3 :1;
    IO_WORD _PC2D0 :1;
    IO_WORD _PC2D1 :1;
    IO_WORD _PC2D2 :1;
    IO_WORD _PC2D3 :1;
  }bit;
  struct{
    IO_WORD :4;
    IO_WORD _BCD :4;
    IO_WORD _PC1D :4;
    IO_WORD _PC2D :4;
  }bitc;
 }CKFCRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _RCFS :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _BCD0 :1;
    IO_BYTE _BCD1 :1;
    IO_BYTE _BCD2 :1;
    IO_BYTE _BCD3 :1;
  }bit;
  struct{
    IO_BYTE :4;
    IO_BYTE _BCD :4;
  }bitc;
 }CKFCRLSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PC1D0 :1;
    IO_BYTE _PC1D1 :1;
    IO_BYTE _PC1D2 :1;
    IO_BYTE _PC1D3 :1;
    IO_BYTE _PC2D0 :1;
    IO_BYTE _PC2D1 :1;
    IO_BYTE _PC2D2 :1;
    IO_BYTE _PC2D3 :1;
  }bit;
  struct{
    IO_BYTE _PC1D :4;
    IO_BYTE _PC2D :4;
  }bitc;
 }CKFCRHSTR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _PMS0 :1;
    IO_WORD _PMS1 :1;
    IO_WORD _PMS2 :1;
    IO_WORD _PMS3 :1;
    IO_WORD _PMS4 :1;
    IO_WORD _VMS0 :1;
    IO_WORD _VMS1 :1;
    IO_WORD _VMS2 :1;
    IO_WORD _PC3D0 :1;
    IO_WORD _PC3D1 :1;
    IO_WORD _PC3D2 :1;
    IO_WORD _PC3D3 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD _PMS :5;
    IO_WORD _VMS :3;
    IO_WORD _PC3D :4;
  }bitc;
 }PLLCRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PMS0 :1;
    IO_BYTE _PMS1 :1;
    IO_BYTE _PMS2 :1;
    IO_BYTE _PMS3 :1;
    IO_BYTE _PMS4 :1;
    IO_BYTE _VMS0 :1;
    IO_BYTE _VMS1 :1;
    IO_BYTE _VMS2 :1;
  }bit;
  struct{
    IO_BYTE _PMS :5;
    IO_BYTE _VMS :3;
  }bitc;
 }PLLCRLSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PC3D0 :1;
    IO_BYTE _PC3D1 :1;
    IO_BYTE _PC3D2 :1;
    IO_BYTE _PC3D3 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _PC3D :4;
  }bitc;
 }PLLCRHSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _RCTI0 :1;
    IO_BYTE _RCTI1 :1;
    IO_BYTE _RCTI2 :1;
    IO_BYTE _RCTI3 :1;
    IO_BYTE _RCTR :1;
    IO_BYTE _RCTIF :1;
    IO_BYTE _RCTIE :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _RCTI :4;
  }bitc;
 }RCTCRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MCTI0 :1;
    IO_BYTE _MCTI1 :1;
    IO_BYTE _MCTI2 :1;
    IO_BYTE _MCTI3 :1;
    IO_BYTE _MCTR :1;
    IO_BYTE _MCTIF :1;
    IO_BYTE _MCTIE :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _MCTI :4;
  }bitc;
 }MCTCRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PRST :1;
    IO_BYTE _ERST :1;
    IO_BYTE _MCRST :1;
    IO_BYTE  :1;
    IO_BYTE _SRST :1;
    IO_BYTE _WRST :1;
    IO_BYTE _MCMF :1;
    IO_BYTE  :1;
  }bit;
 }RCCSRCSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SRSTG :1;
    IO_BYTE _LVRE :1;
    IO_BYTE _LVDE :1;
    IO_BYTE _CSDRE :1;
    IO_BYTE _MCSDI :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }RCRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PRST :1;
    IO_BYTE _ERST :1;
    IO_BYTE _MCRST :1;
    IO_BYTE  :1;
    IO_BYTE _SRST :1;
    IO_BYTE _WRST :1;
    IO_BYTE _MCMF :1;
    IO_BYTE  :1;
  }bit;
 }RCCSRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _WTI0 :1;
    IO_BYTE _WTI1 :1;
    IO_BYTE _WTI2 :1;
    IO_BYTE _WTI3 :1;
    IO_BYTE _WTCS0 :1;
    IO_BYTE _WTCS1 :1;
    IO_BYTE _RSTP :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _WTI :4;
    IO_BYTE _WTCS :2;
  }bitc;
 }WDTCSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _WCP0 :1;
    IO_BYTE _WCP1 :1;
    IO_BYTE _WCP2 :1;
    IO_BYTE _WCP3 :1;
    IO_BYTE _WCP4 :1;
    IO_BYTE _WCP5 :1;
    IO_BYTE _WCP6 :1;
    IO_BYTE _WCP7 :1;
  }bit;
  struct{
    IO_BYTE _WCP :8;
  }bitc;
 }WDTCPSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CKOE0 :1;
    IO_BYTE _CKOXE0 :1;
    IO_BYTE _RUNC0 :1;
    IO_BYTE _RUNM0 :1;
    IO_BYTE _CKOE1 :1;
    IO_BYTE _CKOXE1 :1;
    IO_BYTE _RUNC1 :1;
    IO_BYTE _RUNM1 :1;
  }bit;
 }COARSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SEL0 :1;
    IO_BYTE _SEL1 :1;
    IO_BYTE _SEL2 :1;
    IO_BYTE _SEL3 :1;
    IO_BYTE _DIV0 :1;
    IO_BYTE _DIV1 :1;
    IO_BYTE _DIV2 :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _SEL :4;
    IO_BYTE _DIV :3;
  }bitc;
 }COCR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SEL0 :1;
    IO_BYTE _SEL1 :1;
    IO_BYTE _SEL2 :1;
    IO_BYTE _SEL3 :1;
    IO_BYTE _DIV0 :1;
    IO_BYTE _DIV1 :1;
    IO_BYTE _DIV2 :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _SEL :4;
    IO_BYTE _DIV :3;
  }bitc;
 }COCR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PDX :1;
    IO_BYTE _MODEN :1;
    IO_BYTE _MODRUN :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }CMCRSTR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _C0 :1;
    IO_WORD _C1 :1;
    IO_WORD _C2 :1;
    IO_WORD _C3 :1;
    IO_WORD _C4 :1;
    IO_WORD _N0 :1;
    IO_WORD _N1 :1;
    IO_WORD _N2 :1;
    IO_WORD _N3 :1;
    IO_WORD _K0 :1;
    IO_WORD _K1 :1;
    IO_WORD _K2 :1;
    IO_WORD _K3 :1;
    IO_WORD _K4 :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD _C :5;
    IO_WORD _N :3;
    IO_WORD :1;
    IO_WORD _K :5;
  }bitc;
 }CMPRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _C0 :1;
    IO_BYTE _C1 :1;
    IO_BYTE _C2 :1;
    IO_BYTE _C3 :1;
    IO_BYTE _C4 :1;
    IO_BYTE _N0 :1;
    IO_BYTE _N1 :1;
    IO_BYTE _N2 :1;
  }bit;
  struct{
    IO_BYTE _C :5;
    IO_BYTE _N :3;
  }bitc;
 }CMPRLSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _N3 :1;
    IO_BYTE _K0 :1;
    IO_BYTE _K1 :1;
    IO_BYTE _K2 :1;
    IO_BYTE _K3 :1;
    IO_BYTE _K4 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE :1;
    IO_BYTE _K :5;
  }bitc;
 }CMPRHSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _LPBM0 :1;
    IO_BYTE _LPBM1 :1;
    IO_BYTE _LPMB2 :1;
    IO_BYTE _LPMA0 :1;
    IO_BYTE _LPMA1 :1;
    IO_BYTE _LPMA2 :1;
    IO_BYTE _HPM0 :1;
    IO_BYTE _HPM1 :1;
  }bit;
  struct{
    IO_BYTE _LPBM :3;
    IO_BYTE _LPMA :3;
    IO_BYTE _HPM :2;
  }bitc;
 }VRCRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _D0 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D7 :1;
  }bit;
 }DDR00STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _D0 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D7 :1;
  }bit;
 }DDR01STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _D0 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D7 :1;
  }bit;
 }DDR02STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _D0 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D7 :1;
  }bit;
 }DDR03STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _D0 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D7 :1;
  }bit;
 }DDR04STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _D0 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D7 :1;
  }bit;
 }DDR05STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _D0 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D7 :1;
  }bit;
 }DDR06STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _D0 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D7 :1;
  }bit;
 }DDR07STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _D0 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D7 :1;
  }bit;
 }DDR08STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _D0 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D7 :1;
  }bit;
 }DDR09STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _D0 :1;
    IO_BYTE _D1 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }DDR10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IE0 :1;
    IO_BYTE _IE1 :1;
    IO_BYTE _IE2 :1;
    IO_BYTE _IE3 :1;
    IO_BYTE _IE4 :1;
    IO_BYTE _IE5 :1;
    IO_BYTE _IE6 :1;
    IO_BYTE _IE7 :1;
  }bit;
 }PIER00STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IE0 :1;
    IO_BYTE _IE1 :1;
    IO_BYTE _IE2 :1;
    IO_BYTE _IE3 :1;
    IO_BYTE _IE4 :1;
    IO_BYTE _IE5 :1;
    IO_BYTE _IE6 :1;
    IO_BYTE _IE7 :1;
  }bit;
 }PIER01STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IE0 :1;
    IO_BYTE _IE1 :1;
    IO_BYTE _IE2 :1;
    IO_BYTE _IE3 :1;
    IO_BYTE _IE4 :1;
    IO_BYTE _IE5 :1;
    IO_BYTE _IE6 :1;
    IO_BYTE _IE7 :1;
  }bit;
 }PIER02STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IE0 :1;
    IO_BYTE _IE1 :1;
    IO_BYTE _IE2 :1;
    IO_BYTE _IE3 :1;
    IO_BYTE _IE4 :1;
    IO_BYTE _IE5 :1;
    IO_BYTE _IE6 :1;
    IO_BYTE _IE7 :1;
  }bit;
 }PIER03STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IE0 :1;
    IO_BYTE _IE1 :1;
    IO_BYTE _IE2 :1;
    IO_BYTE _IE3 :1;
    IO_BYTE _IE4 :1;
    IO_BYTE _IE5 :1;
    IO_BYTE _IE6 :1;
    IO_BYTE _IE7 :1;
  }bit;
 }PIER04STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IE0 :1;
    IO_BYTE _IE1 :1;
    IO_BYTE _IE2 :1;
    IO_BYTE _IE3 :1;
    IO_BYTE _IE4 :1;
    IO_BYTE _IE5 :1;
    IO_BYTE _IE6 :1;
    IO_BYTE _IE7 :1;
  }bit;
 }PIER05STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IE0 :1;
    IO_BYTE _IE1 :1;
    IO_BYTE _IE2 :1;
    IO_BYTE _IE3 :1;
    IO_BYTE _IE4 :1;
    IO_BYTE _IE5 :1;
    IO_BYTE _IE6 :1;
    IO_BYTE _IE7 :1;
  }bit;
 }PIER06STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IE0 :1;
    IO_BYTE _IE1 :1;
    IO_BYTE _IE2 :1;
    IO_BYTE _IE3 :1;
    IO_BYTE _IE4 :1;
    IO_BYTE _IE5 :1;
    IO_BYTE _IE6 :1;
    IO_BYTE _IE7 :1;
  }bit;
 }PIER07STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IE0 :1;
    IO_BYTE _IE1 :1;
    IO_BYTE _IE2 :1;
    IO_BYTE _IE3 :1;
    IO_BYTE _IE4 :1;
    IO_BYTE _IE5 :1;
    IO_BYTE _IE6 :1;
    IO_BYTE _IE7 :1;
  }bit;
 }PIER08STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IE0 :1;
    IO_BYTE _IE1 :1;
    IO_BYTE _IE2 :1;
    IO_BYTE _IE3 :1;
    IO_BYTE _IE4 :1;
    IO_BYTE _IE5 :1;
    IO_BYTE _IE6 :1;
    IO_BYTE _IE7 :1;
  }bit;
 }PIER09STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IE0 :1;
    IO_BYTE _IE1 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }PIER10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IL0 :1;
    IO_BYTE _IL1 :1;
    IO_BYTE _IL2 :1;
    IO_BYTE _IL3 :1;
    IO_BYTE _IL4 :1;
    IO_BYTE _IL5 :1;
    IO_BYTE _IL6 :1;
    IO_BYTE _IL7 :1;
  }bit;
 }PILR00STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IL0 :1;
    IO_BYTE _IL1 :1;
    IO_BYTE _IL2 :1;
    IO_BYTE _IL3 :1;
    IO_BYTE _IL4 :1;
    IO_BYTE _IL5 :1;
    IO_BYTE _IL6 :1;
    IO_BYTE _IL7 :1;
  }bit;
 }PILR01STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IL0 :1;
    IO_BYTE _IL1 :1;
    IO_BYTE _IL2 :1;
    IO_BYTE _IL3 :1;
    IO_BYTE _IL4 :1;
    IO_BYTE _IL5 :1;
    IO_BYTE _IL6 :1;
    IO_BYTE _IL7 :1;
  }bit;
 }PILR02STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IL0 :1;
    IO_BYTE _IL1 :1;
    IO_BYTE _IL2 :1;
    IO_BYTE _IL3 :1;
    IO_BYTE _IL4 :1;
    IO_BYTE _IL5 :1;
    IO_BYTE _IL6 :1;
    IO_BYTE _IL7 :1;
  }bit;
 }PILR03STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IL0 :1;
    IO_BYTE _IL1 :1;
    IO_BYTE _IL2 :1;
    IO_BYTE _IL3 :1;
    IO_BYTE _IL4 :1;
    IO_BYTE _IL5 :1;
    IO_BYTE _IL6 :1;
    IO_BYTE _IL7 :1;
  }bit;
 }PILR04STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IL0 :1;
    IO_BYTE _IL1 :1;
    IO_BYTE _IL2 :1;
    IO_BYTE _IL3 :1;
    IO_BYTE _IL4 :1;
    IO_BYTE _IL5 :1;
    IO_BYTE _IL6 :1;
    IO_BYTE _IL7 :1;
  }bit;
 }PILR05STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IL0 :1;
    IO_BYTE _IL1 :1;
    IO_BYTE _IL2 :1;
    IO_BYTE _IL3 :1;
    IO_BYTE _IL4 :1;
    IO_BYTE _IL5 :1;
    IO_BYTE _IL6 :1;
    IO_BYTE _IL7 :1;
  }bit;
 }PILR06STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IL0 :1;
    IO_BYTE _IL1 :1;
    IO_BYTE _IL2 :1;
    IO_BYTE _IL3 :1;
    IO_BYTE _IL4 :1;
    IO_BYTE _IL5 :1;
    IO_BYTE _IL6 :1;
    IO_BYTE _IL7 :1;
  }bit;
 }PILR07STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IL0 :1;
    IO_BYTE _IL1 :1;
    IO_BYTE _IL2 :1;
    IO_BYTE _IL3 :1;
    IO_BYTE _IL4 :1;
    IO_BYTE _IL5 :1;
    IO_BYTE _IL6 :1;
    IO_BYTE _IL7 :1;
  }bit;
 }PILR08STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IL0 :1;
    IO_BYTE _IL1 :1;
    IO_BYTE _IL2 :1;
    IO_BYTE _IL3 :1;
    IO_BYTE _IL4 :1;
    IO_BYTE _IL5 :1;
    IO_BYTE _IL6 :1;
    IO_BYTE _IL7 :1;
  }bit;
 }PILR09STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IL0 :1;
    IO_BYTE _IL1 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }PILR10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EIL0 :1;
    IO_BYTE _EIL1 :1;
    IO_BYTE _EIL2 :1;
    IO_BYTE _EIL3 :1;
    IO_BYTE _EIL4 :1;
    IO_BYTE _EIL5 :1;
    IO_BYTE _EIL6 :1;
    IO_BYTE _EIL7 :1;
  }bit;
 }EPILR00STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EIL0 :1;
    IO_BYTE _EIL1 :1;
    IO_BYTE _EIL2 :1;
    IO_BYTE _EIL3 :1;
    IO_BYTE _EIL4 :1;
    IO_BYTE _EIL5 :1;
    IO_BYTE _EIL6 :1;
    IO_BYTE _EIL7 :1;
  }bit;
 }EPILR01STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EIL0 :1;
    IO_BYTE _EIL1 :1;
    IO_BYTE _EIL2 :1;
    IO_BYTE _EIL3 :1;
    IO_BYTE _EIL4 :1;
    IO_BYTE _EIL5 :1;
    IO_BYTE _EIL6 :1;
    IO_BYTE _EIL7 :1;
  }bit;
 }EPILR02STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EIL0 :1;
    IO_BYTE _EIL1 :1;
    IO_BYTE _EIL2 :1;
    IO_BYTE _EIL3 :1;
    IO_BYTE _EIL4 :1;
    IO_BYTE _EIL5 :1;
    IO_BYTE _EIL6 :1;
    IO_BYTE _EIL7 :1;
  }bit;
 }EPILR03STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EIL0 :1;
    IO_BYTE _EIL1 :1;
    IO_BYTE _EIL2 :1;
    IO_BYTE _EIL3 :1;
    IO_BYTE _EIL4 :1;
    IO_BYTE _EIL5 :1;
    IO_BYTE _EIL6 :1;
    IO_BYTE _EIL7 :1;
  }bit;
 }EPILR04STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EIL0 :1;
    IO_BYTE _EIL1 :1;
    IO_BYTE _EIL2 :1;
    IO_BYTE _EIL3 :1;
    IO_BYTE _EIL4 :1;
    IO_BYTE _EIL5 :1;
    IO_BYTE _EIL6 :1;
    IO_BYTE _EIL7 :1;
  }bit;
 }EPILR05STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EIL0 :1;
    IO_BYTE _EIL1 :1;
    IO_BYTE _EIL2 :1;
    IO_BYTE _EIL3 :1;
    IO_BYTE _EIL4 :1;
    IO_BYTE _EIL5 :1;
    IO_BYTE _EIL6 :1;
    IO_BYTE _EIL7 :1;
  }bit;
 }EPILR06STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EIL0 :1;
    IO_BYTE _EIL1 :1;
    IO_BYTE _EIL2 :1;
    IO_BYTE _EIL3 :1;
    IO_BYTE _EIL4 :1;
    IO_BYTE _EIL5 :1;
    IO_BYTE _EIL6 :1;
    IO_BYTE _EIL7 :1;
  }bit;
 }EPILR07STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EIL0 :1;
    IO_BYTE _EIL1 :1;
    IO_BYTE _EIL2 :1;
    IO_BYTE _EIL3 :1;
    IO_BYTE _EIL4 :1;
    IO_BYTE _EIL5 :1;
    IO_BYTE _EIL6 :1;
    IO_BYTE _EIL7 :1;
  }bit;
 }EPILR08STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EIL0 :1;
    IO_BYTE _EIL1 :1;
    IO_BYTE _EIL2 :1;
    IO_BYTE _EIL3 :1;
    IO_BYTE _EIL4 :1;
    IO_BYTE _EIL5 :1;
    IO_BYTE _EIL6 :1;
    IO_BYTE _EIL7 :1;
  }bit;
 }EPILR09STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EIL0 :1;
    IO_BYTE _EIL1 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }EPILR10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OD0 :1;
    IO_BYTE _OD1 :1;
    IO_BYTE _OD2 :1;
    IO_BYTE _OD3 :1;
    IO_BYTE _OD4 :1;
    IO_BYTE _OD5 :1;
    IO_BYTE _OD6 :1;
    IO_BYTE _OD7 :1;
  }bit;
 }PODR00STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OD0 :1;
    IO_BYTE _OD1 :1;
    IO_BYTE _OD2 :1;
    IO_BYTE _OD3 :1;
    IO_BYTE _OD4 :1;
    IO_BYTE _OD5 :1;
    IO_BYTE _OD6 :1;
    IO_BYTE _OD7 :1;
  }bit;
 }PODR01STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OD0 :1;
    IO_BYTE _OD1 :1;
    IO_BYTE _OD2 :1;
    IO_BYTE _OD3 :1;
    IO_BYTE _OD4 :1;
    IO_BYTE _OD5 :1;
    IO_BYTE _OD6 :1;
    IO_BYTE _OD7 :1;
  }bit;
 }PODR02STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OD0 :1;
    IO_BYTE _OD1 :1;
    IO_BYTE _OD2 :1;
    IO_BYTE _OD3 :1;
    IO_BYTE _OD4 :1;
    IO_BYTE _OD5 :1;
    IO_BYTE _OD6 :1;
    IO_BYTE _OD7 :1;
  }bit;
 }PODR03STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OD0 :1;
    IO_BYTE _OD1 :1;
    IO_BYTE _OD2 :1;
    IO_BYTE _OD3 :1;
    IO_BYTE _OD4 :1;
    IO_BYTE _OD5 :1;
    IO_BYTE _OD6 :1;
    IO_BYTE _OD7 :1;
  }bit;
 }PODR04STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OD0 :1;
    IO_BYTE _OD1 :1;
    IO_BYTE _OD2 :1;
    IO_BYTE _OD3 :1;
    IO_BYTE _OD4 :1;
    IO_BYTE _OD5 :1;
    IO_BYTE _OD6 :1;
    IO_BYTE _OD7 :1;
  }bit;
 }PODR05STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OD0 :1;
    IO_BYTE _OD1 :1;
    IO_BYTE _OD2 :1;
    IO_BYTE _OD3 :1;
    IO_BYTE _OD4 :1;
    IO_BYTE _OD5 :1;
    IO_BYTE _OD6 :1;
    IO_BYTE _OD7 :1;
  }bit;
 }PODR06STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OD0 :1;
    IO_BYTE _OD1 :1;
    IO_BYTE _OD2 :1;
    IO_BYTE _OD3 :1;
    IO_BYTE _OD4 :1;
    IO_BYTE _OD5 :1;
    IO_BYTE _OD6 :1;
    IO_BYTE _OD7 :1;
  }bit;
 }PODR07STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OD0 :1;
    IO_BYTE _OD1 :1;
    IO_BYTE _OD2 :1;
    IO_BYTE _OD3 :1;
    IO_BYTE _OD4 :1;
    IO_BYTE _OD5 :1;
    IO_BYTE _OD6 :1;
    IO_BYTE _OD7 :1;
  }bit;
 }PODR08STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OD0 :1;
    IO_BYTE _OD1 :1;
    IO_BYTE _OD2 :1;
    IO_BYTE _OD3 :1;
    IO_BYTE _OD4 :1;
    IO_BYTE _OD5 :1;
    IO_BYTE _OD6 :1;
    IO_BYTE _OD7 :1;
  }bit;
 }PODR09STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OD0 :1;
    IO_BYTE _OD1 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }PODR10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _HD0 :1;
    IO_BYTE _HD1 :1;
    IO_BYTE _HD2 :1;
    IO_BYTE _HD3 :1;
    IO_BYTE _HD4 :1;
    IO_BYTE _HD5 :1;
    IO_BYTE _HD6 :1;
    IO_BYTE _HD7 :1;
  }bit;
 }PHDR08STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _HD0 :1;
    IO_BYTE _HD1 :1;
    IO_BYTE _HD2 :1;
    IO_BYTE _HD3 :1;
    IO_BYTE _HD4 :1;
    IO_BYTE _HD5 :1;
    IO_BYTE _HD6 :1;
    IO_BYTE _HD7 :1;
  }bit;
 }PHDR09STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _HD0 :1;
    IO_BYTE _HD1 :1;
    IO_BYTE _HD2 :1;
    IO_BYTE _HD3 :1;
    IO_BYTE _HD4 :1;
    IO_BYTE _HD5 :1;
    IO_BYTE _HD6 :1;
    IO_BYTE _HD7 :1;
  }bit;
 }PHDR10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PU0 :1;
    IO_BYTE _PU1 :1;
    IO_BYTE _PU2 :1;
    IO_BYTE _PU3 :1;
    IO_BYTE _PU4 :1;
    IO_BYTE _PU5 :1;
    IO_BYTE _PU6 :1;
    IO_BYTE _PU7 :1;
  }bit;
 }PUCR00STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PU0 :1;
    IO_BYTE _PU1 :1;
    IO_BYTE _PU2 :1;
    IO_BYTE _PU3 :1;
    IO_BYTE _PU4 :1;
    IO_BYTE _PU5 :1;
    IO_BYTE _PU6 :1;
    IO_BYTE _PU7 :1;
  }bit;
 }PUCR01STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PU0 :1;
    IO_BYTE _PU1 :1;
    IO_BYTE _PU2 :1;
    IO_BYTE _PU3 :1;
    IO_BYTE _PU4 :1;
    IO_BYTE _PU5 :1;
    IO_BYTE _PU6 :1;
    IO_BYTE _PU7 :1;
  }bit;
 }PUCR02STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PU0 :1;
    IO_BYTE _PU1 :1;
    IO_BYTE _PU2 :1;
    IO_BYTE _PU3 :1;
    IO_BYTE _PU4 :1;
    IO_BYTE _PU5 :1;
    IO_BYTE _PU6 :1;
    IO_BYTE _PU7 :1;
  }bit;
 }PUCR03STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PU0 :1;
    IO_BYTE _PU1 :1;
    IO_BYTE _PU2 :1;
    IO_BYTE _PU3 :1;
    IO_BYTE _PU4 :1;
    IO_BYTE _PU5 :1;
    IO_BYTE _PU6 :1;
    IO_BYTE _PU7 :1;
  }bit;
 }PUCR04STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PU0 :1;
    IO_BYTE _PU1 :1;
    IO_BYTE _PU2 :1;
    IO_BYTE _PU3 :1;
    IO_BYTE _PU4 :1;
    IO_BYTE _PU5 :1;
    IO_BYTE _PU6 :1;
    IO_BYTE _PU7 :1;
  }bit;
 }PUCR05STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PU0 :1;
    IO_BYTE _PU1 :1;
    IO_BYTE _PU2 :1;
    IO_BYTE _PU3 :1;
    IO_BYTE _PU4 :1;
    IO_BYTE _PU5 :1;
    IO_BYTE _PU6 :1;
    IO_BYTE _PU7 :1;
  }bit;
 }PUCR06STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PU0 :1;
    IO_BYTE _PU1 :1;
    IO_BYTE _PU2 :1;
    IO_BYTE _PU3 :1;
    IO_BYTE _PU4 :1;
    IO_BYTE _PU5 :1;
    IO_BYTE _PU6 :1;
    IO_BYTE _PU7 :1;
  }bit;
 }PUCR07STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PU0 :1;
    IO_BYTE _PU1 :1;
    IO_BYTE _PU2 :1;
    IO_BYTE _PU3 :1;
    IO_BYTE _PU4 :1;
    IO_BYTE _PU5 :1;
    IO_BYTE _PU6 :1;
    IO_BYTE _PU7 :1;
  }bit;
 }PUCR08STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PU0 :1;
    IO_BYTE _PU1 :1;
    IO_BYTE _PU2 :1;
    IO_BYTE _PU3 :1;
    IO_BYTE _PU4 :1;
    IO_BYTE _PU5 :1;
    IO_BYTE _PU6 :1;
    IO_BYTE _PU7 :1;
  }bit;
 }PUCR09STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PU0 :1;
    IO_BYTE _PU1 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }PUCR10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PS0 :1;
    IO_BYTE _PS1 :1;
    IO_BYTE _PS2 :1;
    IO_BYTE _PS3 :1;
    IO_BYTE _PS4 :1;
    IO_BYTE _PS5 :1;
    IO_BYTE _PS6 :1;
    IO_BYTE _PS7 :1;
  }bit;
 }EPSR00STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PS0 :1;
    IO_BYTE _PS1 :1;
    IO_BYTE _PS2 :1;
    IO_BYTE _PS3 :1;
    IO_BYTE _PS4 :1;
    IO_BYTE _PS5 :1;
    IO_BYTE _PS6 :1;
    IO_BYTE _PS7 :1;
  }bit;
 }EPSR01STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PS0 :1;
    IO_BYTE _PS1 :1;
    IO_BYTE _PS2 :1;
    IO_BYTE _PS3 :1;
    IO_BYTE _PS4 :1;
    IO_BYTE _PS5 :1;
    IO_BYTE _PS6 :1;
    IO_BYTE _PS7 :1;
  }bit;
 }EPSR02STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PS0 :1;
    IO_BYTE _PS1 :1;
    IO_BYTE _PS2 :1;
    IO_BYTE _PS3 :1;
    IO_BYTE _PS4 :1;
    IO_BYTE _PS5 :1;
    IO_BYTE _PS6 :1;
    IO_BYTE _PS7 :1;
  }bit;
 }EPSR03STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PS0 :1;
    IO_BYTE _PS1 :1;
    IO_BYTE _PS2 :1;
    IO_BYTE _PS3 :1;
    IO_BYTE _PS4 :1;
    IO_BYTE _PS5 :1;
    IO_BYTE _PS6 :1;
    IO_BYTE _PS7 :1;
  }bit;
 }EPSR04STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PS0 :1;
    IO_BYTE _PS1 :1;
    IO_BYTE _PS2 :1;
    IO_BYTE _PS3 :1;
    IO_BYTE _PS4 :1;
    IO_BYTE _PS5 :1;
    IO_BYTE _PS6 :1;
    IO_BYTE _PS7 :1;
  }bit;
 }EPSR05STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PS0 :1;
    IO_BYTE _PS1 :1;
    IO_BYTE _PS2 :1;
    IO_BYTE _PS3 :1;
    IO_BYTE _PS4 :1;
    IO_BYTE _PS5 :1;
    IO_BYTE _PS6 :1;
    IO_BYTE _PS7 :1;
  }bit;
 }EPSR06STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PS0 :1;
    IO_BYTE _PS1 :1;
    IO_BYTE _PS2 :1;
    IO_BYTE _PS3 :1;
    IO_BYTE _PS4 :1;
    IO_BYTE _PS5 :1;
    IO_BYTE _PS6 :1;
    IO_BYTE _PS7 :1;
  }bit;
 }EPSR07STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PS0 :1;
    IO_BYTE _PS1 :1;
    IO_BYTE _PS2 :1;
    IO_BYTE _PS3 :1;
    IO_BYTE _PS4 :1;
    IO_BYTE _PS5 :1;
    IO_BYTE _PS6 :1;
    IO_BYTE _PS7 :1;
  }bit;
 }EPSR08STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PS0 :1;
    IO_BYTE _PS1 :1;
    IO_BYTE _PS2 :1;
    IO_BYTE _PS3 :1;
    IO_BYTE _PS4 :1;
    IO_BYTE _PS5 :1;
    IO_BYTE _PS6 :1;
    IO_BYTE _PS7 :1;
  }bit;
 }EPSR09STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PS0 :1;
    IO_BYTE _PS1 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }EPSR10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ADE0 :1;
    IO_BYTE _ADE1 :1;
    IO_BYTE _ADE2 :1;
    IO_BYTE _ADE3 :1;
    IO_BYTE _ADE4 :1;
    IO_BYTE _ADE5 :1;
    IO_BYTE _ADE6 :1;
    IO_BYTE _ADE7 :1;
  }bit;
 }ADER0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ADE8 :1;
    IO_BYTE _ADE9 :1;
    IO_BYTE _ADE10 :1;
    IO_BYTE _ADE11 :1;
    IO_BYTE _ADE12 :1;
    IO_BYTE _ADE13 :1;
    IO_BYTE _ADE14 :1;
    IO_BYTE _ADE15 :1;
  }bit;
 }ADER1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ADE16 :1;
    IO_BYTE _ADE17 :1;
    IO_BYTE _ADE18 :1;
    IO_BYTE _ADE19 :1;
    IO_BYTE _ADE20 :1;
    IO_BYTE _ADE21 :1;
    IO_BYTE _ADE22 :1;
    IO_BYTE _ADE23 :1;
  }bit;
 }ADER2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INT0_R :1;
    IO_BYTE _INT1_R :1;
    IO_BYTE _INT2_R :1;
    IO_BYTE _INT3_R :1;
    IO_BYTE _INT4_R :1;
    IO_BYTE _INT5_R :1;
    IO_BYTE _INT6_R :1;
    IO_BYTE _INT7_R :1;
  }bit;
 }PRRR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INT8_R :1;
    IO_BYTE _INT9_R :1;
    IO_BYTE _INT10_R :1;
    IO_BYTE _INT11_R :1;
    IO_BYTE _INT12_R :1;
    IO_BYTE _INT13_R :1;
    IO_BYTE _INT14_R :1;
    IO_BYTE _INT15_R :1;
  }bit;
 }PRRR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PPG0_R :1;
    IO_BYTE _PPG1_R :1;
    IO_BYTE _PPG2_R :1;
    IO_BYTE _PPG3_R :1;
    IO_BYTE _PPG4_R :1;
    IO_BYTE _PPG5_R :1;
    IO_BYTE _PPG6_R :1;
    IO_BYTE _PPG7_R :1;
  }bit;
 }PRRR2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TIN0_R :1;
    IO_BYTE _TOT0_R :1;
    IO_BYTE _TIN1_R :1;
    IO_BYTE _TOT1_R :1;
    IO_BYTE _TIN2_R :1;
    IO_BYTE _TOT2_R :1;
    IO_BYTE _TIN3_R :1;
    IO_BYTE _TOT3_R :1;
  }bit;
 }PRRR3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _IN0_R :1;
    IO_BYTE _IN1_R :1;
    IO_BYTE _IN2_R :1;
    IO_BYTE _IN3_R :1;
    IO_BYTE _IN4_R :1;
    IO_BYTE _IN5_R :1;
    IO_BYTE _IN6_R :1;
    IO_BYTE _IN7_R :1;
  }bit;
 }PRRR4STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OUT0_R :1;
    IO_BYTE _OUT1_R :1;
    IO_BYTE _OUT2_R :1;
    IO_BYTE _OUT3_R :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _OUT6_R :1;
    IO_BYTE _OUT7_R :1;
  }bit;
 }PRRR5STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SGO0_R :1;
    IO_BYTE _SGA0_R :1;
    IO_BYTE _FRCK0_R :1;
    IO_BYTE _SIN2_R :1;
    IO_BYTE _SOT2_R :1;
    IO_BYTE _SCK2_R :1;
    IO_BYTE _CKOT1_R :1;
    IO_BYTE _CKOTX1_R :1;
  }bit;
 }PRRR6STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ADTG_R :1;
    IO_BYTE _NMI_R :1;
    IO_BYTE _CS3_R :1;
    IO_BYTE _INT3_R1 :1;
    IO_BYTE _INT4_R1 :1;
    IO_BYTE _INT5_R1 :1;
    IO_BYTE _RX2_R :1;
    IO_BYTE _TX2_R :1;
  }bit;
 }PRRR7STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SIN7_R :1;
    IO_BYTE _SOT7_R :1;
    IO_BYTE _SCK7_R :1;
    IO_BYTE _SIN8_R :1;
    IO_BYTE _SOT8_R :1;
    IO_BYTE _SCK8_R :1;
    IO_BYTE _SIN9_R :1;
    IO_BYTE _SOT9_R :1;
  }bit;
 }PRRR8STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SCK9_R :1;
    IO_BYTE _SGO1_R :1;
    IO_BYTE _SGA1_R :1;
    IO_BYTE _FRCK2_R :1;
    IO_BYTE _OUT10_R :1;
    IO_BYTE _CKOT0_R :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }PRRR9STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }WTBR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _D0 :1;
    IO_BYTE _D1 :1;
    IO_BYTE _D2 :1;
    IO_BYTE _D3 :1;
    IO_BYTE _D4 :1;
    IO_BYTE _D5 :1;
    IO_BYTE _D6 :1;
    IO_BYTE _D7 :1;
  }bit;
 }WTBRL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _D8 :1;
    IO_BYTE _D9 :1;
    IO_BYTE _D10 :1;
    IO_BYTE _D11 :1;
    IO_BYTE _D12 :1;
    IO_BYTE _D13 :1;
    IO_BYTE _D14 :1;
    IO_BYTE _D15 :1;
  }bit;
 }WTBRH0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _D16 :1;
    IO_BYTE _D17 :1;
    IO_BYTE _D18 :1;
    IO_BYTE _D19 :1;
    IO_BYTE _D20 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _D1 :5;
  }bitc;
 }WTBR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _S0 :1;
    IO_BYTE _S1 :1;
    IO_BYTE _S2 :1;
    IO_BYTE _S3 :1;
    IO_BYTE _S4 :1;
    IO_BYTE _S5 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _S :6;
  }bitc;
 }WTSRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _M0 :1;
    IO_BYTE _M1 :1;
    IO_BYTE _M2 :1;
    IO_BYTE _M3 :1;
    IO_BYTE _M4 :1;
    IO_BYTE _M5 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _M :6;
  }bitc;
 }WTMRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _H0 :1;
    IO_BYTE _H1 :1;
    IO_BYTE _H2 :1;
    IO_BYTE _H3 :1;
    IO_BYTE _H4 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _H :5;
  }bitc;
 }WTHRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INT4 :1;
    IO_BYTE _INTE4 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }WTCERSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CKSEL0 :1;
    IO_BYTE _CKSEL1 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _CKSEL :2;
  }bitc;
 }WTCKSRSTR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _ST :1;
    IO_WORD _OE :1;
    IO_WORD _UPDT :1;
    IO_WORD _RUN :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _INT0 :1;
    IO_WORD _INTE0 :1;
    IO_WORD _INT1 :1;
    IO_WORD _INTE1 :1;
    IO_WORD _INT2 :1;
    IO_WORD _INTE2 :1;
    IO_WORD _INT3 :1;
    IO_WORD _INTE3 :1;
  }bit;
 }WTCRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ST :1;
    IO_BYTE _OE :1;
    IO_BYTE _UPDT :1;
    IO_BYTE _RUN :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }WTCRLSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INT0 :1;
    IO_BYTE _INTE0 :1;
    IO_BYTE _INT1 :1;
    IO_BYTE _INTE1 :1;
    IO_BYTE _INT2 :1;
    IO_BYTE _INTE2 :1;
    IO_BYTE _INT3 :1;
    IO_BYTE _INTE3 :1;
  }bit;
 }WTCRHSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INTEN :1;
    IO_BYTE _INT :1;
    IO_BYTE _CKSEL :1;
    IO_BYTE  :1;
    IO_BYTE _STRT :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _RESV :1;
  }bit;
 }CUCRSTR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TDD0 :1;
    IO_WORD _TDD1 :1;
    IO_WORD _TDD2 :1;
    IO_WORD _TDD3 :1;
    IO_WORD _TDD4 :1;
    IO_WORD _TDD5 :1;
    IO_WORD _TDD6 :1;
    IO_WORD _TDD7 :1;
    IO_WORD _TDD8 :1;
    IO_WORD _TDD9 :1;
    IO_WORD _TDD10 :1;
    IO_WORD _TDD11 :1;
    IO_WORD _TDD12 :1;
    IO_WORD _TDD13 :1;
    IO_WORD _TDD14 :1;
    IO_WORD _TDD15 :1;
  }bit;
  struct{
    IO_WORD _TDD :16;
  }bitc;
 }CUTDSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TDD0 :1;
    IO_BYTE _TDD1 :1;
    IO_BYTE _TDD2 :1;
    IO_BYTE _TDD3 :1;
    IO_BYTE _TDD4 :1;
    IO_BYTE _TDD5 :1;
    IO_BYTE _TDD6 :1;
    IO_BYTE _TDD7 :1;
  }bit;
 }CUTDLSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TDD8 :1;
    IO_BYTE _TDD9 :1;
    IO_BYTE _TDD10 :1;
    IO_BYTE _TDD11 :1;
    IO_BYTE _TDD12 :1;
    IO_BYTE _TDD13 :1;
    IO_BYTE _TDD14 :1;
    IO_BYTE _TDD15 :1;
  }bit;
 }CUTDHSTR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD _TDR0 :1;
    IO_LWORD _TDR1 :1;
    IO_LWORD _TDR2 :1;
    IO_LWORD _TDR3 :1;
    IO_LWORD _TDR4 :1;
    IO_LWORD _TDR5 :1;
    IO_LWORD _TDR6 :1;
    IO_LWORD _TDR7 :1;
    IO_LWORD _TDR8 :1;
    IO_LWORD _TDR9 :1;
    IO_LWORD _TDR10 :1;
    IO_LWORD _TDR11 :1;
    IO_LWORD _TDR12 :1;
    IO_LWORD _TDR13 :1;
    IO_LWORD _TDR14 :1;
    IO_LWORD _TDR15 :1;
    IO_LWORD _TDR16 :1;
    IO_LWORD _TDR17 :1;
    IO_LWORD _TDR18 :1;
    IO_LWORD _TDR19 :1;
    IO_LWORD _TDR20 :1;
    IO_LWORD _TDR21 :1;
    IO_LWORD _TDR22 :1;
    IO_LWORD _TDR23 :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
  }bit;
 }CUTRSTR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TDR0 :1;
    IO_WORD _TDR1 :1;
    IO_WORD _TDR2 :1;
    IO_WORD _TDR3 :1;
    IO_WORD _TDR4 :1;
    IO_WORD _TDR5 :1;
    IO_WORD _TDR6 :1;
    IO_WORD _TDR7 :1;
    IO_WORD _TDR8 :1;
    IO_WORD _TDR9 :1;
    IO_WORD _TDR10 :1;
    IO_WORD _TDR11 :1;
    IO_WORD _TDR12 :1;
    IO_WORD _TDR13 :1;
    IO_WORD _TDR14 :1;
    IO_WORD _TDR15 :1;
  }bit;
 }CUTR2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TDR0 :1;
    IO_BYTE _TDR1 :1;
    IO_BYTE _TDR2 :1;
    IO_BYTE _TDR3 :1;
    IO_BYTE _TDR4 :1;
    IO_BYTE _TDR5 :1;
    IO_BYTE _TDR6 :1;
    IO_BYTE _TDR7 :1;
  }bit;
 }CUTR2LSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TDR8 :1;
    IO_BYTE _TDR9 :1;
    IO_BYTE _TDR10 :1;
    IO_BYTE _TDR11 :1;
    IO_BYTE _TDR12 :1;
    IO_BYTE _TDR13 :1;
    IO_BYTE _TDR14 :1;
    IO_BYTE _TDR15 :1;
  }bit;
 }CUTR2HSTR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TDR16 :1;
    IO_WORD _TDR17 :1;
    IO_WORD _TDR18 :1;
    IO_WORD _TDR19 :1;
    IO_WORD _TDR20 :1;
    IO_WORD _TDR21 :1;
    IO_WORD _TDR22 :1;
    IO_WORD _TDR23 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }CUTR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TDR16 :1;
    IO_BYTE _TDR17 :1;
    IO_BYTE _TDR18 :1;
    IO_BYTE _TDR19 :1;
    IO_BYTE _TDR20 :1;
    IO_BYTE _TDR21 :1;
    IO_BYTE _TDR22 :1;
    IO_BYTE _TDR23 :1;
  }bit;
 }CUTR1LSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }CUTR1HSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TMIS0 :1;
    IO_BYTE _TMIS1 :1;
    IO_BYTE _TMIS2 :1;
    IO_BYTE _TMIS3 :1;
    IO_BYTE _TMIS4 :1;
    IO_BYTE _TMIS5 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }TMISRSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SOE :1;
    IO_BYTE _SCKE :1;
    IO_BYTE _UPCL :1;
    IO_BYTE _REST :1;
    IO_BYTE _EXT :1;
    IO_BYTE _OTO :1;
    IO_BYTE _MD0 :1;
    IO_BYTE _MD1 :1;
  }bit;
  struct{
    IO_BYTE :6;
    IO_BYTE _MD :2;
  }bitc;
 }SMR7STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TXE :1;
    IO_BYTE _RXE :1;
    IO_BYTE _CRE :1;
    IO_BYTE _AD :1;
    IO_BYTE _CL :1;
    IO_BYTE _SBL :1;
    IO_BYTE _P :1;
    IO_BYTE _PEN :1;
  }bit;
 }SCR7STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TIE :1;
    IO_BYTE _RIE :1;
    IO_BYTE _BDS :1;
    IO_BYTE _TDRE :1;
    IO_BYTE _RDRF :1;
    IO_BYTE _FRE :1;
    IO_BYTE _ORE :1;
    IO_BYTE _PE :1;
  }bit;
 }SSR7STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TBI :1;
    IO_BYTE _RBI :1;
    IO_BYTE _BIE :1;
    IO_BYTE _SSM :1;
    IO_BYTE _SCDE :1;
    IO_BYTE _MS :1;
    IO_BYTE _LBR :1;
    IO_BYTE _INV :1;
  }bit;
 }ECCR7STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SCES :1;
    IO_BYTE _CCO :1;
    IO_BYTE _SIOP :1;
    IO_BYTE _SOPE :1;
    IO_BYTE _LBL0 :1;
    IO_BYTE _LBL1 :1;
    IO_BYTE _LBD :1;
    IO_BYTE _LBIE :1;
  }bit;
  struct{
    IO_BYTE :4;
    IO_BYTE _LBL :2;
  }bitc;
 }ESCR7STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _BGR0 :1;
    IO_WORD _BGR1 :1;
    IO_WORD _BGR2 :1;
    IO_WORD _BGR3 :1;
    IO_WORD _BGR4 :1;
    IO_WORD _BGR5 :1;
    IO_WORD _BGR6 :1;
    IO_WORD _BGR7 :1;
    IO_WORD _BGR8 :1;
    IO_WORD _BGR9 :1;
    IO_WORD _BGR10 :1;
    IO_WORD _BGR11 :1;
    IO_WORD _BGR12 :1;
    IO_WORD _BGR13 :1;
    IO_WORD _BGR14 :1;
    IO_WORD _BGR15 :1;
  }bit;
  struct{
    IO_WORD _BGR :16;
  }bitc;
 }BGR7STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _BGR0 :1;
    IO_BYTE _BGR1 :1;
    IO_BYTE _BGR2 :1;
    IO_BYTE _BGR3 :1;
    IO_BYTE _BGR4 :1;
    IO_BYTE _BGR5 :1;
    IO_BYTE _BGR6 :1;
    IO_BYTE _BGR7 :1;
  }bit;
 }BGRL7STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _BGR8 :1;
    IO_BYTE _BGR9 :1;
    IO_BYTE _BGR10 :1;
    IO_BYTE _BGR11 :1;
    IO_BYTE _BGR12 :1;
    IO_BYTE _BGR13 :1;
    IO_BYTE _BGR14 :1;
    IO_BYTE _BGR15 :1;
  }bit;
 }BGRH7STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _AICD :1;
    IO_BYTE _RBI :1;
    IO_BYTE _RDRF :1;
    IO_BYTE _TDRE :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }ESIR7STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SOE :1;
    IO_BYTE _SCKE :1;
    IO_BYTE _UPCL :1;
    IO_BYTE _REST :1;
    IO_BYTE _EXT :1;
    IO_BYTE _OTO :1;
    IO_BYTE _MD0 :1;
    IO_BYTE _MD1 :1;
  }bit;
  struct{
    IO_BYTE :6;
    IO_BYTE _MD :2;
  }bitc;
 }SMR8STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TXE :1;
    IO_BYTE _RXE :1;
    IO_BYTE _CRE :1;
    IO_BYTE _AD :1;
    IO_BYTE _CL :1;
    IO_BYTE _SBL :1;
    IO_BYTE _P :1;
    IO_BYTE _PEN :1;
  }bit;
 }SCR8STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TIE :1;
    IO_BYTE _RIE :1;
    IO_BYTE _BDS :1;
    IO_BYTE _TDRE :1;
    IO_BYTE _RDRF :1;
    IO_BYTE _FRE :1;
    IO_BYTE _ORE :1;
    IO_BYTE _PE :1;
  }bit;
 }SSR8STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TBI :1;
    IO_BYTE _RBI :1;
    IO_BYTE _BIE :1;
    IO_BYTE _SSM :1;
    IO_BYTE _SCDE :1;
    IO_BYTE _MS :1;
    IO_BYTE _LBR :1;
    IO_BYTE _INV :1;
  }bit;
 }ECCR8STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SCES :1;
    IO_BYTE _CCO :1;
    IO_BYTE _SIOP :1;
    IO_BYTE _SOPE :1;
    IO_BYTE _LBL0 :1;
    IO_BYTE _LBL1 :1;
    IO_BYTE _LBD :1;
    IO_BYTE _LBIE :1;
  }bit;
  struct{
    IO_BYTE :4;
    IO_BYTE _LBL :2;
  }bitc;
 }ESCR8STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _BGR0 :1;
    IO_WORD _BGR1 :1;
    IO_WORD _BGR2 :1;
    IO_WORD _BGR3 :1;
    IO_WORD _BGR4 :1;
    IO_WORD _BGR5 :1;
    IO_WORD _BGR6 :1;
    IO_WORD _BGR7 :1;
    IO_WORD _BGR8 :1;
    IO_WORD _BGR9 :1;
    IO_WORD _BGR10 :1;
    IO_WORD _BGR11 :1;
    IO_WORD _BGR12 :1;
    IO_WORD _BGR13 :1;
    IO_WORD _BGR14 :1;
    IO_WORD _BGR15 :1;
  }bit;
  struct{
    IO_WORD _BGR :16;
  }bitc;
 }BGR8STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _BGR0 :1;
    IO_BYTE _BGR1 :1;
    IO_BYTE _BGR2 :1;
    IO_BYTE _BGR3 :1;
    IO_BYTE _BGR4 :1;
    IO_BYTE _BGR5 :1;
    IO_BYTE _BGR6 :1;
    IO_BYTE _BGR7 :1;
  }bit;
 }BGRL8STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _BGR8 :1;
    IO_BYTE _BGR9 :1;
    IO_BYTE _BGR10 :1;
    IO_BYTE _BGR11 :1;
    IO_BYTE _BGR12 :1;
    IO_BYTE _BGR13 :1;
    IO_BYTE _BGR14 :1;
    IO_BYTE _BGR15 :1;
  }bit;
 }BGRH8STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _AICD :1;
    IO_BYTE _RBI :1;
    IO_BYTE _RDRF :1;
    IO_BYTE _TDRE :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }ESIR8STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SOE :1;
    IO_BYTE _SCKE :1;
    IO_BYTE _UPCL :1;
    IO_BYTE _REST :1;
    IO_BYTE _EXT :1;
    IO_BYTE _OTO :1;
    IO_BYTE _MD0 :1;
    IO_BYTE _MD1 :1;
  }bit;
  struct{
    IO_BYTE :6;
    IO_BYTE _MD :2;
  }bitc;
 }SMR9STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TXE :1;
    IO_BYTE _RXE :1;
    IO_BYTE _CRE :1;
    IO_BYTE _AD :1;
    IO_BYTE _CL :1;
    IO_BYTE _SBL :1;
    IO_BYTE _P :1;
    IO_BYTE _PEN :1;
  }bit;
 }SCR9STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TIE :1;
    IO_BYTE _RIE :1;
    IO_BYTE _BDS :1;
    IO_BYTE _TDRE :1;
    IO_BYTE _RDRF :1;
    IO_BYTE _FRE :1;
    IO_BYTE _ORE :1;
    IO_BYTE _PE :1;
  }bit;
 }SSR9STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TBI :1;
    IO_BYTE _RBI :1;
    IO_BYTE _BIE :1;
    IO_BYTE _SSM :1;
    IO_BYTE _SCDE :1;
    IO_BYTE _MS :1;
    IO_BYTE _LBR :1;
    IO_BYTE _INV :1;
  }bit;
 }ECCR9STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _SCES :1;
    IO_BYTE _CCO :1;
    IO_BYTE _SIOP :1;
    IO_BYTE _SOPE :1;
    IO_BYTE _LBL0 :1;
    IO_BYTE _LBL1 :1;
    IO_BYTE _LBD :1;
    IO_BYTE _LBIE :1;
  }bit;
  struct{
    IO_BYTE :4;
    IO_BYTE _LBL :2;
  }bitc;
 }ESCR9STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _BGR0 :1;
    IO_WORD _BGR1 :1;
    IO_WORD _BGR2 :1;
    IO_WORD _BGR3 :1;
    IO_WORD _BGR4 :1;
    IO_WORD _BGR5 :1;
    IO_WORD _BGR6 :1;
    IO_WORD _BGR7 :1;
    IO_WORD _BGR8 :1;
    IO_WORD _BGR9 :1;
    IO_WORD _BGR10 :1;
    IO_WORD _BGR11 :1;
    IO_WORD _BGR12 :1;
    IO_WORD _BGR13 :1;
    IO_WORD _BGR14 :1;
    IO_WORD _BGR15 :1;
  }bit;
  struct{
    IO_WORD _BGR :16;
  }bitc;
 }BGR9STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _BGR0 :1;
    IO_BYTE _BGR1 :1;
    IO_BYTE _BGR2 :1;
    IO_BYTE _BGR3 :1;
    IO_BYTE _BGR4 :1;
    IO_BYTE _BGR5 :1;
    IO_BYTE _BGR6 :1;
    IO_BYTE _BGR7 :1;
  }bit;
 }BGRL9STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _BGR8 :1;
    IO_BYTE _BGR9 :1;
    IO_BYTE _BGR10 :1;
    IO_BYTE _BGR11 :1;
    IO_BYTE _BGR12 :1;
    IO_BYTE _BGR13 :1;
    IO_BYTE _BGR14 :1;
    IO_BYTE _BGR15 :1;
  }bit;
 }BGRH9STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _AICD :1;
    IO_BYTE _RBI :1;
    IO_BYTE _RDRF :1;
    IO_BYTE _TDRE :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }ESIR9STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PD :1;
    IO_BYTE _IEN :1;
    IO_BYTE _IRQ :1;
    IO_BYTE _OUT1 :1;
    IO_BYTE _OUT2 :1;
    IO_BYTE _UVEN :1;
    IO_BYTE _OVEN :1;
    IO_BYTE _CMD :1;
  }bit;
 }ACSR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INTREF :1;
    IO_BYTE  :1;
    IO_BYTE _ACE :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }AECSR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PD :1;
    IO_BYTE _IEN :1;
    IO_BYTE _IRQ :1;
    IO_BYTE _OUT1 :1;
    IO_BYTE _OUT2 :1;
    IO_BYTE _UVEN :1;
    IO_BYTE _OVEN :1;
    IO_BYTE _CMD :1;
  }bit;
 }ACSR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INTREF :1;
    IO_BYTE  :1;
    IO_BYTE _ACE :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }AECSR1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PTMR6STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PCSR6STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PDUT6STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _OSEL :1;
    IO_WORD _OE :1;
    IO_WORD _IRS0 :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRQF :1;
    IO_WORD _IREN :1;
    IO_WORD _EGS0 :1;
    IO_WORD _EGS1 :1;
    IO_WORD  :1;
    IO_WORD _PGMS :1;
    IO_WORD _CKS0 :1;
    IO_WORD _CKS1 :1;
    IO_WORD _RTRG :1;
    IO_WORD _MDSE :1;
    IO_WORD _STGR :1;
    IO_WORD _CNTE :1;
  }bit;
  struct{
    IO_WORD :2;
    IO_WORD _IRS :2;
    IO_WORD :2;
    IO_WORD _EGS :2;
    IO_WORD :2;
    IO_WORD _CKS :2;
  }bitc;
 }PCN6STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OSEL :1;
    IO_BYTE _OE :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IREN :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _EGS1 :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _IRS :2;
    IO_BYTE :2;
    IO_BYTE _EGS :2;
  }bitc;
 }PCNL6STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE _PGMS :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _CNTE :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH6STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PTMR7STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PCSR7STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PDUT7STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _OSEL :1;
    IO_WORD _OE :1;
    IO_WORD _IRS0 :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRQF :1;
    IO_WORD _IREN :1;
    IO_WORD _EGS0 :1;
    IO_WORD _EGS1 :1;
    IO_WORD  :1;
    IO_WORD _PGMS :1;
    IO_WORD _CKS0 :1;
    IO_WORD _CKS1 :1;
    IO_WORD _RTRG :1;
    IO_WORD _MDSE :1;
    IO_WORD _STGR :1;
    IO_WORD _CNTE :1;
  }bit;
  struct{
    IO_WORD :2;
    IO_WORD _IRS :2;
    IO_WORD :2;
    IO_WORD _EGS :2;
    IO_WORD :2;
    IO_WORD _CKS :2;
  }bitc;
 }PCN7STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OSEL :1;
    IO_BYTE _OE :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IREN :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _EGS1 :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _IRS :2;
    IO_BYTE :2;
    IO_BYTE _EGS :2;
  }bitc;
 }PCNL7STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE _PGMS :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _CNTE :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH7STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TSEL00 :1;
    IO_WORD _TSEL01 :1;
    IO_WORD _TSEL02 :1;
    IO_WORD _TSEL03 :1;
    IO_WORD _TSEL10 :1;
    IO_WORD _TSEL11 :1;
    IO_WORD _TSEL12 :1;
    IO_WORD _TSEL13 :1;
    IO_WORD _TSEL20 :1;
    IO_WORD _TSEL21 :1;
    IO_WORD _TSEL22 :1;
    IO_WORD _TSEL23 :1;
    IO_WORD _TSEL30 :1;
    IO_WORD _TSEL31 :1;
    IO_WORD _TSEL32 :1;
    IO_WORD _TSEL33 :1;
  }bit;
  struct{
    IO_WORD _TSEL0 :4;
    IO_WORD _TSEL1 :4;
    IO_WORD _TSEL2 :4;
    IO_WORD _TSEL3 :4;
  }bitc;
 }GCN12STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TSEL00 :1;
    IO_BYTE _TSEL01 :1;
    IO_BYTE _TSEL02 :1;
    IO_BYTE _TSEL03 :1;
    IO_BYTE _TSEL10 :1;
    IO_BYTE _TSEL11 :1;
    IO_BYTE _TSEL12 :1;
    IO_BYTE _TSEL13 :1;
  }bit;
  struct{
    IO_BYTE _TSEL0 :4;
    IO_BYTE _TSEL1 :4;
  }bitc;
 }GCN1L2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TSEL20 :1;
    IO_BYTE _TSEL21 :1;
    IO_BYTE _TSEL22 :1;
    IO_BYTE _TSEL23 :1;
    IO_BYTE _TSEL30 :1;
    IO_BYTE _TSEL31 :1;
    IO_BYTE _TSEL32 :1;
    IO_BYTE _TSEL33 :1;
  }bit;
  struct{
    IO_BYTE _TSEL2 :4;
    IO_BYTE _TSEL3 :4;
  }bitc;
 }GCN1H2STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _EN0 :1;
    IO_WORD _EN1 :1;
    IO_WORD _EN2 :1;
    IO_WORD _EN3 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _CKSEL0 :1;
    IO_WORD _CKSEL1 :1;
    IO_WORD _CKSEL2 :1;
    IO_WORD _CKSEL3 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD _EN :4;
    IO_WORD :4;
    IO_WORD _CKSEL :4;
  }bitc;
 }GCN22STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EN0 :1;
    IO_BYTE _EN1 :1;
    IO_BYTE _EN2 :1;
    IO_BYTE _EN3 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _EN :4;
  }bitc;
 }GCN2L2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CKSEL0 :1;
    IO_BYTE _CKSEL1 :1;
    IO_BYTE _CKSEL2 :1;
    IO_BYTE _CKSEL3 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _CKSEL :4;
  }bitc;
 }GCN2H2STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PTMR8STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PCSR8STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PDUT8STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _OSEL :1;
    IO_WORD _OE :1;
    IO_WORD _IRS0 :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRQF :1;
    IO_WORD _IREN :1;
    IO_WORD _EGS0 :1;
    IO_WORD _EGS1 :1;
    IO_WORD  :1;
    IO_WORD _PGMS :1;
    IO_WORD _CKS0 :1;
    IO_WORD _CKS1 :1;
    IO_WORD _RTRG :1;
    IO_WORD _MDSE :1;
    IO_WORD _STGR :1;
    IO_WORD _CNTE :1;
  }bit;
  struct{
    IO_WORD :2;
    IO_WORD _IRS :2;
    IO_WORD :2;
    IO_WORD _EGS :2;
    IO_WORD :2;
    IO_WORD _CKS :2;
  }bitc;
 }PCN8STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OSEL :1;
    IO_BYTE _OE :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IREN :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _EGS1 :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _IRS :2;
    IO_BYTE :2;
    IO_BYTE _EGS :2;
  }bitc;
 }PCNL8STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE _PGMS :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _CNTE :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH8STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PTMR9STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PCSR9STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PDUT9STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _OSEL :1;
    IO_WORD _OE :1;
    IO_WORD _IRS0 :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRQF :1;
    IO_WORD _IREN :1;
    IO_WORD _EGS0 :1;
    IO_WORD _EGS1 :1;
    IO_WORD  :1;
    IO_WORD _PGMS :1;
    IO_WORD _CKS0 :1;
    IO_WORD _CKS1 :1;
    IO_WORD _RTRG :1;
    IO_WORD _MDSE :1;
    IO_WORD _STGR :1;
    IO_WORD _CNTE :1;
  }bit;
  struct{
    IO_WORD :2;
    IO_WORD _IRS :2;
    IO_WORD :2;
    IO_WORD _EGS :2;
    IO_WORD :2;
    IO_WORD _CKS :2;
  }bitc;
 }PCN9STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OSEL :1;
    IO_BYTE _OE :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IREN :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _EGS1 :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _IRS :2;
    IO_BYTE :2;
    IO_BYTE _EGS :2;
  }bitc;
 }PCNL9STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE _PGMS :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _CNTE :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH9STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PTMR10STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PCSR10STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PDUT10STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _OSEL :1;
    IO_WORD _OE :1;
    IO_WORD _IRS0 :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRQF :1;
    IO_WORD _IREN :1;
    IO_WORD _EGS0 :1;
    IO_WORD _EGS1 :1;
    IO_WORD  :1;
    IO_WORD _PGMS :1;
    IO_WORD _CKS0 :1;
    IO_WORD _CKS1 :1;
    IO_WORD _RTRG :1;
    IO_WORD _MDSE :1;
    IO_WORD _STGR :1;
    IO_WORD _CNTE :1;
  }bit;
  struct{
    IO_WORD :2;
    IO_WORD _IRS :2;
    IO_WORD :2;
    IO_WORD _EGS :2;
    IO_WORD :2;
    IO_WORD _CKS :2;
  }bitc;
 }PCN10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OSEL :1;
    IO_BYTE _OE :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IREN :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _EGS1 :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _IRS :2;
    IO_BYTE :2;
    IO_BYTE _EGS :2;
  }bitc;
 }PCNL10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE _PGMS :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _CNTE :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH10STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PTMR11STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PCSR11STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PDUT11STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _OSEL :1;
    IO_WORD _OE :1;
    IO_WORD _IRS0 :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRQF :1;
    IO_WORD _IREN :1;
    IO_WORD _EGS0 :1;
    IO_WORD _EGS1 :1;
    IO_WORD  :1;
    IO_WORD _PGMS :1;
    IO_WORD _CKS0 :1;
    IO_WORD _CKS1 :1;
    IO_WORD _RTRG :1;
    IO_WORD _MDSE :1;
    IO_WORD _STGR :1;
    IO_WORD _CNTE :1;
  }bit;
  struct{
    IO_WORD :2;
    IO_WORD _IRS :2;
    IO_WORD :2;
    IO_WORD _EGS :2;
    IO_WORD :2;
    IO_WORD _CKS :2;
  }bitc;
 }PCN11STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OSEL :1;
    IO_BYTE _OE :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IREN :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _EGS1 :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _IRS :2;
    IO_BYTE :2;
    IO_BYTE _EGS :2;
  }bitc;
 }PCNL11STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE _PGMS :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _CNTE :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH11STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TSEL00 :1;
    IO_WORD _TSEL01 :1;
    IO_WORD _TSEL02 :1;
    IO_WORD _TSEL03 :1;
    IO_WORD _TSEL10 :1;
    IO_WORD _TSEL11 :1;
    IO_WORD _TSEL12 :1;
    IO_WORD _TSEL13 :1;
    IO_WORD _TSEL20 :1;
    IO_WORD _TSEL21 :1;
    IO_WORD _TSEL22 :1;
    IO_WORD _TSEL23 :1;
    IO_WORD _TSEL30 :1;
    IO_WORD _TSEL31 :1;
    IO_WORD _TSEL32 :1;
    IO_WORD _TSEL33 :1;
  }bit;
  struct{
    IO_WORD _TSEL0 :4;
    IO_WORD _TSEL1 :4;
    IO_WORD _TSEL2 :4;
    IO_WORD _TSEL3 :4;
  }bitc;
 }GCN13STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TSEL00 :1;
    IO_BYTE _TSEL01 :1;
    IO_BYTE _TSEL02 :1;
    IO_BYTE _TSEL03 :1;
    IO_BYTE _TSEL10 :1;
    IO_BYTE _TSEL11 :1;
    IO_BYTE _TSEL12 :1;
    IO_BYTE _TSEL13 :1;
  }bit;
  struct{
    IO_BYTE _TSEL0 :4;
    IO_BYTE _TSEL1 :4;
  }bitc;
 }GCN1L3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TSEL20 :1;
    IO_BYTE _TSEL21 :1;
    IO_BYTE _TSEL22 :1;
    IO_BYTE _TSEL23 :1;
    IO_BYTE _TSEL30 :1;
    IO_BYTE _TSEL31 :1;
    IO_BYTE _TSEL32 :1;
    IO_BYTE _TSEL33 :1;
  }bit;
  struct{
    IO_BYTE _TSEL2 :4;
    IO_BYTE _TSEL3 :4;
  }bitc;
 }GCN1H3STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _EN0 :1;
    IO_WORD _EN1 :1;
    IO_WORD _EN2 :1;
    IO_WORD _EN3 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _CKSEL0 :1;
    IO_WORD _CKSEL1 :1;
    IO_WORD _CKSEL2 :1;
    IO_WORD _CKSEL3 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD _EN :4;
    IO_WORD :4;
    IO_WORD _CKSEL :4;
  }bitc;
 }GCN23STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EN0 :1;
    IO_BYTE _EN1 :1;
    IO_BYTE _EN2 :1;
    IO_BYTE _EN3 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _EN :4;
  }bitc;
 }GCN2L3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CKSEL0 :1;
    IO_BYTE _CKSEL1 :1;
    IO_BYTE _CKSEL2 :1;
    IO_BYTE _CKSEL3 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _CKSEL :4;
  }bitc;
 }GCN2H3STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PTMR12STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PCSR12STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PDUT12STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _OSEL :1;
    IO_WORD _OE :1;
    IO_WORD _IRS0 :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRQF :1;
    IO_WORD _IREN :1;
    IO_WORD _EGS0 :1;
    IO_WORD _EGS1 :1;
    IO_WORD  :1;
    IO_WORD _PGMS :1;
    IO_WORD _CKS0 :1;
    IO_WORD _CKS1 :1;
    IO_WORD _RTRG :1;
    IO_WORD _MDSE :1;
    IO_WORD _STGR :1;
    IO_WORD _CNTE :1;
  }bit;
  struct{
    IO_WORD :2;
    IO_WORD _IRS :2;
    IO_WORD :2;
    IO_WORD _EGS :2;
    IO_WORD :2;
    IO_WORD _CKS :2;
  }bitc;
 }PCN12STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OSEL :1;
    IO_BYTE _OE :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IREN :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _EGS1 :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _IRS :2;
    IO_BYTE :2;
    IO_BYTE _EGS :2;
  }bitc;
 }PCNL12STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE _PGMS :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _CNTE :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH12STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PTMR13STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PCSR13STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PDUT13STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _OSEL :1;
    IO_WORD _OE :1;
    IO_WORD _IRS0 :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRQF :1;
    IO_WORD _IREN :1;
    IO_WORD _EGS0 :1;
    IO_WORD _EGS1 :1;
    IO_WORD  :1;
    IO_WORD _PGMS :1;
    IO_WORD _CKS0 :1;
    IO_WORD _CKS1 :1;
    IO_WORD _RTRG :1;
    IO_WORD _MDSE :1;
    IO_WORD _STGR :1;
    IO_WORD _CNTE :1;
  }bit;
  struct{
    IO_WORD :2;
    IO_WORD _IRS :2;
    IO_WORD :2;
    IO_WORD _EGS :2;
    IO_WORD :2;
    IO_WORD _CKS :2;
  }bitc;
 }PCN13STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OSEL :1;
    IO_BYTE _OE :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IREN :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _EGS1 :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _IRS :2;
    IO_BYTE :2;
    IO_BYTE _EGS :2;
  }bitc;
 }PCNL13STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE _PGMS :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _CNTE :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH13STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PTMR14STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PCSR14STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PDUT14STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _OSEL :1;
    IO_WORD _OE :1;
    IO_WORD _IRS0 :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRQF :1;
    IO_WORD _IREN :1;
    IO_WORD _EGS0 :1;
    IO_WORD _EGS1 :1;
    IO_WORD  :1;
    IO_WORD _PGMS :1;
    IO_WORD _CKS0 :1;
    IO_WORD _CKS1 :1;
    IO_WORD _RTRG :1;
    IO_WORD _MDSE :1;
    IO_WORD _STGR :1;
    IO_WORD _CNTE :1;
  }bit;
  struct{
    IO_WORD :2;
    IO_WORD _IRS :2;
    IO_WORD :2;
    IO_WORD _EGS :2;
    IO_WORD :2;
    IO_WORD _CKS :2;
  }bitc;
 }PCN14STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OSEL :1;
    IO_BYTE _OE :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IREN :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _EGS1 :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _IRS :2;
    IO_BYTE :2;
    IO_BYTE _EGS :2;
  }bitc;
 }PCNL14STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE _PGMS :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _CNTE :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH14STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PTMR15STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PCSR15STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _D0 :1;
    IO_WORD _D1 :1;
    IO_WORD _D2 :1;
    IO_WORD _D3 :1;
    IO_WORD _D4 :1;
    IO_WORD _D5 :1;
    IO_WORD _D6 :1;
    IO_WORD _D7 :1;
    IO_WORD _D8 :1;
    IO_WORD _D9 :1;
    IO_WORD _D10 :1;
    IO_WORD _D11 :1;
    IO_WORD _D12 :1;
    IO_WORD _D13 :1;
    IO_WORD _D14 :1;
    IO_WORD _D15 :1;
  }bit;
  struct{
    IO_WORD _D :16;
  }bitc;
 }PDUT15STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _OSEL :1;
    IO_WORD _OE :1;
    IO_WORD _IRS0 :1;
    IO_WORD _IRS1 :1;
    IO_WORD _IRQF :1;
    IO_WORD _IREN :1;
    IO_WORD _EGS0 :1;
    IO_WORD _EGS1 :1;
    IO_WORD  :1;
    IO_WORD _PGMS :1;
    IO_WORD _CKS0 :1;
    IO_WORD _CKS1 :1;
    IO_WORD _RTRG :1;
    IO_WORD _MDSE :1;
    IO_WORD _STGR :1;
    IO_WORD _CNTE :1;
  }bit;
  struct{
    IO_WORD :2;
    IO_WORD _IRS :2;
    IO_WORD :2;
    IO_WORD _EGS :2;
    IO_WORD :2;
    IO_WORD _CKS :2;
  }bitc;
 }PCN15STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OSEL :1;
    IO_BYTE _OE :1;
    IO_BYTE _IRS0 :1;
    IO_BYTE _IRS1 :1;
    IO_BYTE _IRQF :1;
    IO_BYTE _IREN :1;
    IO_BYTE _EGS0 :1;
    IO_BYTE _EGS1 :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _IRS :2;
    IO_BYTE :2;
    IO_BYTE _EGS :2;
  }bitc;
 }PCNL15STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE _PGMS :1;
    IO_BYTE _CKS0 :1;
    IO_BYTE _CKS1 :1;
    IO_BYTE _RTRG :1;
    IO_BYTE _MDSE :1;
    IO_BYTE _STGR :1;
    IO_BYTE _CNTE :1;
  }bit;
  struct{
    IO_BYTE :2;
    IO_BYTE _CKS :2;
  }bitc;
 }PCNH15STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PPG8_R :1;
    IO_BYTE _PPG9_R :1;
    IO_BYTE _PPG10_R :1;
    IO_BYTE _PPG11_R :1;
    IO_BYTE _TTG8_R :1;
    IO_BYTE _TTG9_R :1;
    IO_BYTE _TTG10_R :1;
    IO_BYTE _TTG11_R :1;
  }bit;
 }PRRR10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _PPG16_R :1;
    IO_BYTE _PPG17_R :1;
    IO_BYTE _PPG18_R :1;
    IO_BYTE _PPG19_R :1;
    IO_BYTE _TTG16_R :1;
    IO_BYTE _TTG17_R :1;
    IO_BYTE _TTG18_R :1;
    IO_BYTE _TTG19_R :1;
  }bit;
 }PRRR11STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _CS0_R :1;
    IO_BYTE _CS1_R :1;
    IO_BYTE _CS2_R :1;
    IO_BYTE _CS4_R :1;
    IO_BYTE _CS5_R :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }PRRR12STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }PRRR13STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _R0 :1;
    IO_WORD _R1 :1;
    IO_WORD _R2 :1;
    IO_WORD _ACE :1;
    IO_WORD _STS :1;
    IO_WORD _WSF :1;
    IO_WORD _ES :1;
    IO_WORD _BW :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _CSE :1;
    IO_WORD _CSL :1;
    IO_WORD _ATL :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD _R :3;
  }bitc;
 }EAC0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _R0 :1;
    IO_BYTE _R1 :1;
    IO_BYTE _R2 :1;
    IO_BYTE _ACE :1;
    IO_BYTE _STS :1;
    IO_BYTE _WSF :1;
    IO_BYTE _ES :1;
    IO_BYTE _BW :1;
  }bit;
  struct{
    IO_BYTE _R :3;
  }bitc;
 }EACL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _CSE :1;
    IO_BYTE _CSL :1;
    IO_BYTE _ATL :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }EACH0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _R0 :1;
    IO_WORD _R1 :1;
    IO_WORD _R2 :1;
    IO_WORD _ACE :1;
    IO_WORD _STS :1;
    IO_WORD _WSF :1;
    IO_WORD _ES :1;
    IO_WORD _BW :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _CSE :1;
    IO_WORD _CSL :1;
    IO_WORD _ATL :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD _R :3;
  }bitc;
 }EAC1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _R0 :1;
    IO_BYTE _R1 :1;
    IO_BYTE _R2 :1;
    IO_BYTE _ACE :1;
    IO_BYTE _STS :1;
    IO_BYTE _WSF :1;
    IO_BYTE _ES :1;
    IO_BYTE _BW :1;
  }bit;
  struct{
    IO_BYTE _R :3;
  }bitc;
 }EACL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _CSE :1;
    IO_BYTE _CSL :1;
    IO_BYTE _ATL :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }EACH1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _R0 :1;
    IO_WORD _R1 :1;
    IO_WORD _R2 :1;
    IO_WORD _ACE :1;
    IO_WORD _STS :1;
    IO_WORD _WSF :1;
    IO_WORD _ES :1;
    IO_WORD _BW :1;
    IO_WORD _EASZ0 :1;
    IO_WORD _EASZ1 :1;
    IO_WORD _EASZ2 :1;
    IO_WORD _CSE :1;
    IO_WORD _CSL :1;
    IO_WORD _ATL :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD _R :3;
    IO_WORD :5;
    IO_WORD _EASZ :3;
  }bitc;
 }EAC2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _R0 :1;
    IO_BYTE _R1 :1;
    IO_BYTE _R2 :1;
    IO_BYTE _ACE :1;
    IO_BYTE _STS :1;
    IO_BYTE _WSF :1;
    IO_BYTE _ES :1;
    IO_BYTE _BW :1;
  }bit;
  struct{
    IO_BYTE _R :3;
  }bitc;
 }EACL2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EASZ0 :1;
    IO_BYTE _EASZ1 :1;
    IO_BYTE _EASZ2 :1;
    IO_BYTE _CSE :1;
    IO_BYTE _CSL :1;
    IO_BYTE _ATL :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _EASZ :3;
  }bitc;
 }EACH2STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _R0 :1;
    IO_WORD _R1 :1;
    IO_WORD _R2 :1;
    IO_WORD _ACE :1;
    IO_WORD _STS :1;
    IO_WORD _WSF :1;
    IO_WORD _ES :1;
    IO_WORD _BW :1;
    IO_WORD _EASZ0 :1;
    IO_WORD _EASZ1 :1;
    IO_WORD _EASZ2 :1;
    IO_WORD _CSE :1;
    IO_WORD _CSL :1;
    IO_WORD _ATL :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD _R :3;
    IO_WORD :5;
    IO_WORD _EASZ :3;
  }bitc;
 }EAC3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _R0 :1;
    IO_BYTE _R1 :1;
    IO_BYTE _R2 :1;
    IO_BYTE _ACE :1;
    IO_BYTE _STS :1;
    IO_BYTE _WSF :1;
    IO_BYTE _ES :1;
    IO_BYTE _BW :1;
  }bit;
  struct{
    IO_BYTE _R :3;
  }bitc;
 }EACL3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EASZ0 :1;
    IO_BYTE _EASZ1 :1;
    IO_BYTE _EASZ2 :1;
    IO_BYTE _CSE :1;
    IO_BYTE _CSL :1;
    IO_BYTE _ATL :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _EASZ :3;
  }bitc;
 }EACH3STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _R0 :1;
    IO_WORD _R1 :1;
    IO_WORD _R2 :1;
    IO_WORD _ACE :1;
    IO_WORD _STS :1;
    IO_WORD _WSF :1;
    IO_WORD _ES :1;
    IO_WORD _BW :1;
    IO_WORD _EASZ0 :1;
    IO_WORD _EASZ1 :1;
    IO_WORD _EASZ2 :1;
    IO_WORD _CSE :1;
    IO_WORD _CSL :1;
    IO_WORD _ATL :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD _R :3;
    IO_WORD :5;
    IO_WORD _EASZ :3;
  }bitc;
 }EAC4STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _R0 :1;
    IO_BYTE _R1 :1;
    IO_BYTE _R2 :1;
    IO_BYTE _ACE :1;
    IO_BYTE _STS :1;
    IO_BYTE _WSF :1;
    IO_BYTE _ES :1;
    IO_BYTE _BW :1;
  }bit;
  struct{
    IO_BYTE _R :3;
  }bitc;
 }EACL4STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EASZ0 :1;
    IO_BYTE _EASZ1 :1;
    IO_BYTE _EASZ2 :1;
    IO_BYTE _CSE :1;
    IO_BYTE _CSL :1;
    IO_BYTE _ATL :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _EASZ :3;
  }bitc;
 }EACH4STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _R0 :1;
    IO_WORD _R1 :1;
    IO_WORD _R2 :1;
    IO_WORD _ACE :1;
    IO_WORD _STS :1;
    IO_WORD _WSF :1;
    IO_WORD _ES :1;
    IO_WORD _BW :1;
    IO_WORD _EASZ0 :1;
    IO_WORD _EASZ1 :1;
    IO_WORD _EASZ2 :1;
    IO_WORD _CSE :1;
    IO_WORD _CSL :1;
    IO_WORD _ATL :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD _R :3;
    IO_WORD :5;
    IO_WORD _EASZ :3;
  }bitc;
 }EAC5STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _R0 :1;
    IO_BYTE _R1 :1;
    IO_BYTE _R2 :1;
    IO_BYTE _ACE :1;
    IO_BYTE _STS :1;
    IO_BYTE _WSF :1;
    IO_BYTE _ES :1;
    IO_BYTE _BW :1;
  }bit;
  struct{
    IO_BYTE _R :3;
  }bitc;
 }EACL5STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EASZ0 :1;
    IO_BYTE _EASZ1 :1;
    IO_BYTE _EASZ2 :1;
    IO_BYTE _CSE :1;
    IO_BYTE _CSL :1;
    IO_BYTE _ATL :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _EASZ :3;
  }bitc;
 }EACH5STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _A0 :1;
    IO_BYTE _A1 :1;
    IO_BYTE _A2 :1;
    IO_BYTE _A3 :1;
    IO_BYTE _A4 :1;
    IO_BYTE _A5 :1;
    IO_BYTE _A6 :1;
    IO_BYTE _A7 :1;
  }bit;
  struct{
    IO_BYTE _A :8;
  }bitc;
 }EAS2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _A0 :1;
    IO_BYTE _A1 :1;
    IO_BYTE _A2 :1;
    IO_BYTE _A3 :1;
    IO_BYTE _A4 :1;
    IO_BYTE _A5 :1;
    IO_BYTE _A6 :1;
    IO_BYTE _A7 :1;
  }bit;
  struct{
    IO_BYTE _A :8;
  }bitc;
 }EAS3STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _A0 :1;
    IO_BYTE _A1 :1;
    IO_BYTE _A2 :1;
    IO_BYTE _A3 :1;
    IO_BYTE _A4 :1;
    IO_BYTE _A5 :1;
    IO_BYTE _A6 :1;
    IO_BYTE _A7 :1;
  }bit;
  struct{
    IO_BYTE _A :8;
  }bitc;
 }EAS4STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _A0 :1;
    IO_BYTE _A1 :1;
    IO_BYTE _A2 :1;
    IO_BYTE _A3 :1;
    IO_BYTE _A4 :1;
    IO_BYTE _A5 :1;
    IO_BYTE _A6 :1;
    IO_BYTE _A7 :1;
  }bit;
 }EAS5STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _EAE0 :1;
    IO_BYTE _EAE1 :1;
    IO_BYTE _EAE2 :1;
    IO_BYTE _EAE3 :1;
    IO_BYTE _EAE4 :1;
    IO_BYTE _EAE5 :1;
    IO_BYTE _ERE :1;
    IO_BYTE _NMS :1;
  }bit;
  struct{
    IO_BYTE _EAE :6;
  }bitc;
 }EBMSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _DIV0 :1;
    IO_BYTE _DIV1 :1;
    IO_BYTE _DIV2 :1;
    IO_BYTE _CSM :1;
    IO_BYTE _CKI :1;
    IO_BYTE _CKE :1;
    IO_BYTE _RYE :1;
    IO_BYTE _HDE :1;
  }bit;
  struct{
    IO_BYTE _DIV :3;
  }bitc;
 }EBCFSTR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _A00 :1;
    IO_BYTE _A01 :1;
    IO_BYTE _A02 :1;
    IO_BYTE _A03 :1;
    IO_BYTE _A04 :1;
    IO_BYTE _A05 :1;
    IO_BYTE _A06 :1;
    IO_BYTE _A07 :1;
  }bit;
 }EBAE0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _A08 :1;
    IO_BYTE _A09 :1;
    IO_BYTE _A10 :1;
    IO_BYTE _A11 :1;
    IO_BYTE _A12 :1;
    IO_BYTE _A13 :1;
    IO_BYTE _A14 :1;
    IO_BYTE _A15 :1;
  }bit;
 }EBAE1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _A16 :1;
    IO_BYTE _A17 :1;
    IO_BYTE _A18 :1;
    IO_BYTE _A19 :1;
    IO_BYTE _A20 :1;
    IO_BYTE _A21 :1;
    IO_BYTE _A22 :1;
    IO_BYTE _A23 :1;
  }bit;
 }EBAE2STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _LBE :1;
    IO_BYTE _UBE :1;
    IO_BYTE _WRLE :1;
    IO_BYTE _WRHE :1;
    IO_BYTE _RDE :1;
    IO_BYTE _ASE :1;
    IO_BYTE _ASL :1;
    IO_BYTE  :1;
  }bit;
 }EBCSSTR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _INIT :1;
    IO_WORD _IE :1;
    IO_WORD _SIE :1;
    IO_WORD _EIE :1;
    IO_WORD  :1;
    IO_WORD _DAR :1;
    IO_WORD _CCE :1;
    IO_WORD _TEST :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }CTRLR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INIT :1;
    IO_BYTE _IE :1;
    IO_BYTE _SIE :1;
    IO_BYTE _EIE :1;
    IO_BYTE  :1;
    IO_BYTE _DAR :1;
    IO_BYTE _CCE :1;
    IO_BYTE _TEST :1;
  }bit;
 }CTRLRL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }CTRLRH0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _LEC0 :1;
    IO_WORD _LEC1 :1;
    IO_WORD _LEC2 :1;
    IO_WORD _TXOK :1;
    IO_WORD _RXOK :1;
    IO_WORD _EPASS :1;
    IO_WORD _EWARN :1;
    IO_WORD _BOFF :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD _LEC :3;
  }bitc;
 }STATR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _LEC0 :1;
    IO_BYTE _LEC1 :1;
    IO_BYTE _LEC2 :1;
    IO_BYTE _TXOK :1;
    IO_BYTE _RXOK :1;
    IO_BYTE _EPASS :1;
    IO_BYTE _EWARN :1;
    IO_BYTE _BOFF :1;
  }bit;
  struct{
    IO_BYTE _LEC :3;
  }bitc;
 }STATRL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }STATRH0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TEC0 :1;
    IO_WORD _TEC1 :1;
    IO_WORD _TEC2 :1;
    IO_WORD _TEC3 :1;
    IO_WORD _TEC4 :1;
    IO_WORD _TEC5 :1;
    IO_WORD _TEC6 :1;
    IO_WORD _TEC7 :1;
    IO_WORD _REC0 :1;
    IO_WORD _REC1 :1;
    IO_WORD _REC2 :1;
    IO_WORD _REC3 :1;
    IO_WORD _REC4 :1;
    IO_WORD _REC5 :1;
    IO_WORD _REC6 :1;
    IO_WORD _RP :1;
  }bit;
  struct{
    IO_WORD _TEC :8;
    IO_WORD _REC :7;
  }bitc;
 }ERRCNT0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TEC0 :1;
    IO_BYTE _TEC1 :1;
    IO_BYTE _TEC2 :1;
    IO_BYTE _TEC3 :1;
    IO_BYTE _TEC4 :1;
    IO_BYTE _TEC5 :1;
    IO_BYTE _TEC6 :1;
    IO_BYTE _TEC7 :1;
  }bit;
  struct{
    IO_BYTE _TEC :8;
  }bitc;
 }ERRCNTL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _REC0 :1;
    IO_BYTE _REC1 :1;
    IO_BYTE _REC2 :1;
    IO_BYTE _REC3 :1;
    IO_BYTE _REC4 :1;
    IO_BYTE _REC5 :1;
    IO_BYTE _REC6 :1;
    IO_BYTE _RP :1;
  }bit;
  struct{
    IO_BYTE _REC :7;
  }bitc;
 }ERRCNTH0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _BRP0 :1;
    IO_WORD _BRP1 :1;
    IO_WORD _BRP2 :1;
    IO_WORD _BRP3 :1;
    IO_WORD _BRP4 :1;
    IO_WORD _BRP5 :1;
    IO_WORD _SJW0 :1;
    IO_WORD _SJW1 :1;
    IO_WORD _TSEG10 :1;
    IO_WORD _TSEG11 :1;
    IO_WORD _TSEG12 :1;
    IO_WORD _TSEG13 :1;
    IO_WORD _TSEG20 :1;
    IO_WORD _TSEG21 :1;
    IO_WORD _TSEG22 :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD _BRP :6;
    IO_WORD _SJW :2;
    IO_WORD _TSEG1 :4;
    IO_WORD _TSEG2 :3;
  }bitc;
 }BTR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _BRP0 :1;
    IO_BYTE _BRP1 :1;
    IO_BYTE _BRP2 :1;
    IO_BYTE _BRP3 :1;
    IO_BYTE _BRP4 :1;
    IO_BYTE _BRP5 :1;
    IO_BYTE _SJW0 :1;
    IO_BYTE _SJW1 :1;
  }bit;
  struct{
    IO_BYTE _BRP :6;
    IO_BYTE _SJW :2;
  }bitc;
 }BTRL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TSEG10 :1;
    IO_BYTE _TSEG11 :1;
    IO_BYTE _TSEG12 :1;
    IO_BYTE _TSEG13 :1;
    IO_BYTE _TSEG20 :1;
    IO_BYTE _TSEG21 :1;
    IO_BYTE _TSEG22 :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _TSEG1 :4;
    IO_BYTE _TSEG2 :3;
  }bitc;
 }BTRH0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _INTID0 :1;
    IO_WORD _INTID1 :1;
    IO_WORD _INTID2 :1;
    IO_WORD _INTID3 :1;
    IO_WORD _INTID4 :1;
    IO_WORD _INTID5 :1;
    IO_WORD _INTID6 :1;
    IO_WORD _INTID7 :1;
    IO_WORD _INTID8 :1;
    IO_WORD _INTID9 :1;
    IO_WORD _INTID10 :1;
    IO_WORD _INTID11 :1;
    IO_WORD _INTID12 :1;
    IO_WORD _INTID13 :1;
    IO_WORD _INTID14 :1;
    IO_WORD _INTID15 :1;
  }bit;
  struct{
    IO_WORD _INTID :16;
  }bitc;
 }INTR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INTID0 :1;
    IO_BYTE _INTID1 :1;
    IO_BYTE _INTID2 :1;
    IO_BYTE _INTID3 :1;
    IO_BYTE _INTID4 :1;
    IO_BYTE _INTID5 :1;
    IO_BYTE _INTID6 :1;
    IO_BYTE _INTID7 :1;
  }bit;
 }INTRL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INTID8 :1;
    IO_BYTE _INTID9 :1;
    IO_BYTE _INTID10 :1;
    IO_BYTE _INTID11 :1;
    IO_BYTE _INTID12 :1;
    IO_BYTE _INTID13 :1;
    IO_BYTE _INTID14 :1;
    IO_BYTE _INTID15 :1;
  }bit;
 }INTRH0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _BASIC :1;
    IO_WORD _SILENT :1;
    IO_WORD _LBACK :1;
    IO_WORD _TX0 :1;
    IO_WORD _TX1 :1;
    IO_WORD _RX :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }TESTR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _BASIC :1;
    IO_BYTE _SILENT :1;
    IO_BYTE _LBACK :1;
    IO_BYTE _TX0 :1;
    IO_BYTE _TX1 :1;
    IO_BYTE _RX :1;
  }bit;
 }TESTRL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }TESTRH0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _BRPE0 :1;
    IO_WORD _BRPE1 :1;
    IO_WORD _BRPE2 :1;
    IO_WORD _BRPE3 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD _BRPE :4;
  }bitc;
 }BRPER0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _BRPE0 :1;
    IO_BYTE _BRPE1 :1;
    IO_BYTE _BRPE2 :1;
    IO_BYTE _BRPE3 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _BRPE :4;
  }bitc;
 }BRPERL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }BRPERH0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _MSGN0 :1;
    IO_WORD _MSGN1 :1;
    IO_WORD _MSGN2 :1;
    IO_WORD _MSGN3 :1;
    IO_WORD _MSGN4 :1;
    IO_WORD _MSGN5 :1;
    IO_WORD _MSGN6 :1;
    IO_WORD _MSGN7 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _BUSY :1;
  }bit;
 }IF1CREQ0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSGN0 :1;
    IO_BYTE _MSGN1 :1;
    IO_BYTE _MSGN2 :1;
    IO_BYTE _MSGN3 :1;
    IO_BYTE _MSGN4 :1;
    IO_BYTE _MSGN5 :1;
    IO_BYTE _MSGN6 :1;
    IO_BYTE _MSGN7 :1;
  }bit;
 }IF1CREQL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _BUSY :1;
  }bit;
 }IF1CREQH0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _DATAB :1;
    IO_WORD _DATAA :1;
    IO_WORD _TXREQ :1;
    IO_WORD _CIP :1;
    IO_WORD _CONTROL :1;
    IO_WORD _ARB :1;
    IO_WORD _MASK :1;
    IO_WORD _WRRD :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF1CMSK0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _DATAB :1;
    IO_BYTE _DATAA :1;
    IO_BYTE _TXREQ :1;
    IO_BYTE _CIP :1;
    IO_BYTE _CONTROL :1;
    IO_BYTE _ARB :1;
    IO_BYTE _MASK :1;
    IO_BYTE _WRRD :1;
  }bit;
 }IF1CMSKL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF1CMSKH0STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD _MSK0 :1;
    IO_LWORD _MSK1 :1;
    IO_LWORD _MSK2 :1;
    IO_LWORD _MSK3 :1;
    IO_LWORD _MSK4 :1;
    IO_LWORD _MSK5 :1;
    IO_LWORD _MSK6 :1;
    IO_LWORD _MSK7 :1;
    IO_LWORD _MSK8 :1;
    IO_LWORD _MSK9 :1;
    IO_LWORD _MSK10 :1;
    IO_LWORD _MSK11 :1;
    IO_LWORD _MSK12 :1;
    IO_LWORD _MSK13 :1;
    IO_LWORD _MSK14 :1;
    IO_LWORD _MSK15 :1;
    IO_LWORD _MSK16 :1;
    IO_LWORD _MSK17 :1;
    IO_LWORD _MSK18 :1;
    IO_LWORD _MSK19 :1;
    IO_LWORD _MSK20 :1;
    IO_LWORD _MSK21 :1;
    IO_LWORD _MSK22 :1;
    IO_LWORD _MSK23 :1;
    IO_LWORD _MSK24 :1;
    IO_LWORD _MSK25 :1;
    IO_LWORD _MSK26 :1;
    IO_LWORD _MSK27 :1;
    IO_LWORD _MSK28 :1;
    IO_LWORD  :1;
    IO_LWORD _MDIR :1;
    IO_LWORD _MXTD :1;
  }bit;
  struct{
    IO_LWORD _MSK :29;
  }bitc;
 }IF1MSK0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _MSK0 :1;
    IO_WORD _MSK1 :1;
    IO_WORD _MSK2 :1;
    IO_WORD _MSK3 :1;
    IO_WORD _MSK4 :1;
    IO_WORD _MSK5 :1;
    IO_WORD _MSK6 :1;
    IO_WORD _MSK7 :1;
    IO_WORD _MSK8 :1;
    IO_WORD _MSK9 :1;
    IO_WORD _MSK10 :1;
    IO_WORD _MSK11 :1;
    IO_WORD _MSK12 :1;
    IO_WORD _MSK13 :1;
    IO_WORD _MSK14 :1;
    IO_WORD _MSK15 :1;
  }bit;
 }IF1MSK10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSK0 :1;
    IO_BYTE _MSK1 :1;
    IO_BYTE _MSK2 :1;
    IO_BYTE _MSK3 :1;
    IO_BYTE _MSK4 :1;
    IO_BYTE _MSK5 :1;
    IO_BYTE _MSK6 :1;
    IO_BYTE _MSK7 :1;
  }bit;
 }IF1MSK1L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSK8 :1;
    IO_BYTE _MSK9 :1;
    IO_BYTE _MSK10 :1;
    IO_BYTE _MSK11 :1;
    IO_BYTE _MSK12 :1;
    IO_BYTE _MSK13 :1;
    IO_BYTE _MSK14 :1;
    IO_BYTE _MSK15 :1;
  }bit;
 }IF1MSK1H0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _MSK16 :1;
    IO_WORD _MSK17 :1;
    IO_WORD _MSK18 :1;
    IO_WORD _MSK19 :1;
    IO_WORD _MSK20 :1;
    IO_WORD _MSK21 :1;
    IO_WORD _MSK22 :1;
    IO_WORD _MSK23 :1;
    IO_WORD _MSK24 :1;
    IO_WORD _MSK25 :1;
    IO_WORD _MSK26 :1;
    IO_WORD _MSK27 :1;
    IO_WORD _MSK28 :1;
    IO_WORD  :1;
    IO_WORD _MDIR :1;
    IO_WORD _MXTD :1;
  }bit;
 }IF1MSK20STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSK16 :1;
    IO_BYTE _MSK17 :1;
    IO_BYTE _MSK18 :1;
    IO_BYTE _MSK19 :1;
    IO_BYTE _MSK20 :1;
    IO_BYTE _MSK21 :1;
    IO_BYTE _MSK22 :1;
    IO_BYTE _MSK23 :1;
  }bit;
 }IF1MSK2L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSK24 :1;
    IO_BYTE _MSK25 :1;
    IO_BYTE _MSK26 :1;
    IO_BYTE _MSK27 :1;
    IO_BYTE _MSK28 :1;
    IO_BYTE  :1;
    IO_BYTE _MDIR :1;
    IO_BYTE _MXTD :1;
  }bit;
 }IF1MSK2H0STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD _ID0 :1;
    IO_LWORD _ID1 :1;
    IO_LWORD _ID2 :1;
    IO_LWORD _ID3 :1;
    IO_LWORD _ID4 :1;
    IO_LWORD _ID5 :1;
    IO_LWORD _ID6 :1;
    IO_LWORD _ID7 :1;
    IO_LWORD _ID8 :1;
    IO_LWORD _ID9 :1;
    IO_LWORD _ID10 :1;
    IO_LWORD _ID11 :1;
    IO_LWORD _ID12 :1;
    IO_LWORD _ID13 :1;
    IO_LWORD _ID14 :1;
    IO_LWORD _ID15 :1;
    IO_LWORD _ID16 :1;
    IO_LWORD _ID17 :1;
    IO_LWORD _ID18 :1;
    IO_LWORD _ID19 :1;
    IO_LWORD _ID20 :1;
    IO_LWORD _ID21 :1;
    IO_LWORD _ID22 :1;
    IO_LWORD _ID23 :1;
    IO_LWORD _ID24 :1;
    IO_LWORD _ID25 :1;
    IO_LWORD _ID26 :1;
    IO_LWORD _ID27 :1;
    IO_LWORD _ID28 :1;
    IO_LWORD _DIR :1;
    IO_LWORD _XTD :1;
    IO_LWORD _MSGVAL :1;
  }bit;
  struct{
    IO_LWORD _ID :29;
  }bitc;
 }IF1ARB0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _ID0 :1;
    IO_WORD _ID1 :1;
    IO_WORD _ID2 :1;
    IO_WORD _ID3 :1;
    IO_WORD _ID4 :1;
    IO_WORD _ID5 :1;
    IO_WORD _ID6 :1;
    IO_WORD _ID7 :1;
    IO_WORD _ID8 :1;
    IO_WORD _ID9 :1;
    IO_WORD _ID10 :1;
    IO_WORD _ID11 :1;
    IO_WORD _ID12 :1;
    IO_WORD _ID13 :1;
    IO_WORD _ID14 :1;
    IO_WORD _ID15 :1;
  }bit;
 }IF1ARB10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ID0 :1;
    IO_BYTE _ID1 :1;
    IO_BYTE _ID2 :1;
    IO_BYTE _ID3 :1;
    IO_BYTE _ID4 :1;
    IO_BYTE _ID5 :1;
    IO_BYTE _ID6 :1;
    IO_BYTE _ID7 :1;
  }bit;
 }IF1ARB1L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ID8 :1;
    IO_BYTE _ID9 :1;
    IO_BYTE _ID10 :1;
    IO_BYTE _ID11 :1;
    IO_BYTE _ID12 :1;
    IO_BYTE _ID13 :1;
    IO_BYTE _ID14 :1;
    IO_BYTE _ID15 :1;
  }bit;
 }IF1ARB1H0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _ID16 :1;
    IO_WORD _ID17 :1;
    IO_WORD _ID18 :1;
    IO_WORD _ID19 :1;
    IO_WORD _ID20 :1;
    IO_WORD _ID21 :1;
    IO_WORD _ID22 :1;
    IO_WORD _ID23 :1;
    IO_WORD _ID24 :1;
    IO_WORD _ID25 :1;
    IO_WORD _ID26 :1;
    IO_WORD _ID27 :1;
    IO_WORD _ID28 :1;
    IO_WORD _DIR :1;
    IO_WORD _XTD :1;
    IO_WORD _MSGVAL :1;
  }bit;
 }IF1ARB20STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ID16 :1;
    IO_BYTE _ID17 :1;
    IO_BYTE _ID18 :1;
    IO_BYTE _ID19 :1;
    IO_BYTE _ID20 :1;
    IO_BYTE _ID21 :1;
    IO_BYTE _ID22 :1;
    IO_BYTE _ID23 :1;
  }bit;
 }IF1ARB2L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ID24 :1;
    IO_BYTE _ID25 :1;
    IO_BYTE _ID26 :1;
    IO_BYTE _ID27 :1;
    IO_BYTE _ID28 :1;
    IO_BYTE _DIR :1;
    IO_BYTE _XTD :1;
    IO_BYTE _MSGVAL :1;
  }bit;
 }IF1ARB2H0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _DLC0 :1;
    IO_WORD _DLC1 :1;
    IO_WORD _DLC2 :1;
    IO_WORD _DLC3 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _EOB :1;
    IO_WORD _TXRQST :1;
    IO_WORD _RMTEN :1;
    IO_WORD _RXIE :1;
    IO_WORD _TXIE :1;
    IO_WORD _UMASK :1;
    IO_WORD _INTPND :1;
    IO_WORD _MSGLST :1;
    IO_WORD _NEWDAT :1;
  }bit;
  struct{
    IO_WORD _DLC :4;
  }bitc;
 }IF1MCTR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _DLC0 :1;
    IO_BYTE _DLC1 :1;
    IO_BYTE _DLC2 :1;
    IO_BYTE _DLC3 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _EOB :1;
  }bit;
  struct{
    IO_BYTE _DLC :4;
  }bitc;
 }IF1MCTRL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TXRQST :1;
    IO_BYTE _RMTEN :1;
    IO_BYTE _RXIE :1;
    IO_BYTE _TXIE :1;
    IO_BYTE _UMASK :1;
    IO_BYTE _INTPND :1;
    IO_BYTE _MSGLST :1;
    IO_BYTE _NEWDAT :1;
  }bit;
 }IF1MCTRH0STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
  }bit;
 }IF1DTA0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF1DTA10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF1DTA1L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF1DTA1H0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF1DTA20STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF1DTA2L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF1DTA2H0STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
  }bit;
 }IF1DTB0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF1DTB10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF1DTB1L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF1DTB1H0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF1DTB20STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF1DTB2L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF1DTB2H0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _MSGN0 :1;
    IO_WORD _MSGN1 :1;
    IO_WORD _MSGN2 :1;
    IO_WORD _MSGN3 :1;
    IO_WORD _MSGN4 :1;
    IO_WORD _MSGN5 :1;
    IO_WORD _MSGN6 :1;
    IO_WORD _MSGN7 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _BUSY :1;
  }bit;
 }IF2CREQ0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSGN0 :1;
    IO_BYTE _MSGN1 :1;
    IO_BYTE _MSGN2 :1;
    IO_BYTE _MSGN3 :1;
    IO_BYTE _MSGN4 :1;
    IO_BYTE _MSGN5 :1;
    IO_BYTE _MSGN6 :1;
    IO_BYTE _MSGN7 :1;
  }bit;
 }IF2CREQL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _BUSY :1;
  }bit;
 }IF2CREQH0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _DATAB :1;
    IO_WORD _DATAA :1;
    IO_WORD _TXREQ :1;
    IO_WORD _CIP :1;
    IO_WORD _CONTROL :1;
    IO_WORD _ARB :1;
    IO_WORD _MASK :1;
    IO_WORD _WRRD :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF2CMSK0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _DATAB :1;
    IO_BYTE _DATAA :1;
    IO_BYTE _TXREQ :1;
    IO_BYTE _CIP :1;
    IO_BYTE _CONTROL :1;
    IO_BYTE _ARB :1;
    IO_BYTE _MASK :1;
    IO_BYTE _WRRD :1;
  }bit;
 }IF2CMSKL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF2CMSKH0STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD _MSK0 :1;
    IO_LWORD _MSK1 :1;
    IO_LWORD _MSK2 :1;
    IO_LWORD _MSK3 :1;
    IO_LWORD _MSK4 :1;
    IO_LWORD _MSK5 :1;
    IO_LWORD _MSK6 :1;
    IO_LWORD _MSK7 :1;
    IO_LWORD _MSK8 :1;
    IO_LWORD _MSK9 :1;
    IO_LWORD _MSK10 :1;
    IO_LWORD _MSK11 :1;
    IO_LWORD _MSK12 :1;
    IO_LWORD _MSK13 :1;
    IO_LWORD _MSK14 :1;
    IO_LWORD _MSK15 :1;
    IO_LWORD _MSK16 :1;
    IO_LWORD _MSK17 :1;
    IO_LWORD _MSK18 :1;
    IO_LWORD _MSK19 :1;
    IO_LWORD _MSK20 :1;
    IO_LWORD _MSK21 :1;
    IO_LWORD _MSK22 :1;
    IO_LWORD _MSK23 :1;
    IO_LWORD _MSK24 :1;
    IO_LWORD _MSK25 :1;
    IO_LWORD _MSK26 :1;
    IO_LWORD _MSK27 :1;
    IO_LWORD _MSK28 :1;
    IO_LWORD  :1;
    IO_LWORD _MDIR :1;
    IO_LWORD _MXTD :1;
  }bit;
  struct{
    IO_LWORD _MSK :29;
  }bitc;
 }IF2MSK0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _MSK0 :1;
    IO_WORD _MSK1 :1;
    IO_WORD _MSK2 :1;
    IO_WORD _MSK3 :1;
    IO_WORD _MSK4 :1;
    IO_WORD _MSK5 :1;
    IO_WORD _MSK6 :1;
    IO_WORD _MSK7 :1;
    IO_WORD _MSK8 :1;
    IO_WORD _MSK9 :1;
    IO_WORD _MSK10 :1;
    IO_WORD _MSK11 :1;
    IO_WORD _MSK12 :1;
    IO_WORD _MSK13 :1;
    IO_WORD _MSK14 :1;
    IO_WORD _MSK15 :1;
  }bit;
 }IF2MSK10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSK0 :1;
    IO_BYTE _MSK1 :1;
    IO_BYTE _MSK2 :1;
    IO_BYTE _MSK3 :1;
    IO_BYTE _MSK4 :1;
    IO_BYTE _MSK5 :1;
    IO_BYTE _MSK6 :1;
    IO_BYTE _MSK7 :1;
  }bit;
 }IF2MSK1L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSK8 :1;
    IO_BYTE _MSK9 :1;
    IO_BYTE _MSK10 :1;
    IO_BYTE _MSK11 :1;
    IO_BYTE _MSK12 :1;
    IO_BYTE _MSK13 :1;
    IO_BYTE _MSK14 :1;
    IO_BYTE _MSK15 :1;
  }bit;
 }IF2MSK1H0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _MSK16 :1;
    IO_WORD _MSK17 :1;
    IO_WORD _MSK18 :1;
    IO_WORD _MSK19 :1;
    IO_WORD _MSK20 :1;
    IO_WORD _MSK21 :1;
    IO_WORD _MSK22 :1;
    IO_WORD _MSK23 :1;
    IO_WORD _MSK24 :1;
    IO_WORD _MSK25 :1;
    IO_WORD _MSK26 :1;
    IO_WORD _MSK27 :1;
    IO_WORD _MSK28 :1;
    IO_WORD  :1;
    IO_WORD _MDIR :1;
    IO_WORD _MXTD :1;
  }bit;
 }IF2MSK20STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSK16 :1;
    IO_BYTE _MSK17 :1;
    IO_BYTE _MSK18 :1;
    IO_BYTE _MSK19 :1;
    IO_BYTE _MSK20 :1;
    IO_BYTE _MSK21 :1;
    IO_BYTE _MSK22 :1;
    IO_BYTE _MSK23 :1;
  }bit;
 }IF2MSK2L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSK24 :1;
    IO_BYTE _MSK25 :1;
    IO_BYTE _MSK26 :1;
    IO_BYTE _MSK27 :1;
    IO_BYTE _MSK28 :1;
    IO_BYTE  :1;
    IO_BYTE _MDIR :1;
    IO_BYTE _MXTD :1;
  }bit;
 }IF2MSK2H0STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD _ID0 :1;
    IO_LWORD _ID1 :1;
    IO_LWORD _ID2 :1;
    IO_LWORD _ID3 :1;
    IO_LWORD _ID4 :1;
    IO_LWORD _ID5 :1;
    IO_LWORD _ID6 :1;
    IO_LWORD _ID7 :1;
    IO_LWORD _ID8 :1;
    IO_LWORD _ID9 :1;
    IO_LWORD _ID10 :1;
    IO_LWORD _ID11 :1;
    IO_LWORD _ID12 :1;
    IO_LWORD _ID13 :1;
    IO_LWORD _ID14 :1;
    IO_LWORD _ID15 :1;
    IO_LWORD _ID16 :1;
    IO_LWORD _ID17 :1;
    IO_LWORD _ID18 :1;
    IO_LWORD _ID19 :1;
    IO_LWORD _ID20 :1;
    IO_LWORD _ID21 :1;
    IO_LWORD _ID22 :1;
    IO_LWORD _ID23 :1;
    IO_LWORD _ID24 :1;
    IO_LWORD _ID25 :1;
    IO_LWORD _ID26 :1;
    IO_LWORD _ID27 :1;
    IO_LWORD _ID28 :1;
    IO_LWORD _DIR :1;
    IO_LWORD _XTD :1;
    IO_LWORD _MSGVAL :1;
  }bit;
  struct{
    IO_LWORD _ID :29;
  }bitc;
 }IF2ARB0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _ID0 :1;
    IO_WORD _ID1 :1;
    IO_WORD _ID2 :1;
    IO_WORD _ID3 :1;
    IO_WORD _ID4 :1;
    IO_WORD _ID5 :1;
    IO_WORD _ID6 :1;
    IO_WORD _ID7 :1;
    IO_WORD _ID8 :1;
    IO_WORD _ID9 :1;
    IO_WORD _ID10 :1;
    IO_WORD _ID11 :1;
    IO_WORD _ID12 :1;
    IO_WORD _ID13 :1;
    IO_WORD _ID14 :1;
    IO_WORD _ID15 :1;
  }bit;
 }IF2ARB10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ID0 :1;
    IO_BYTE _ID1 :1;
    IO_BYTE _ID2 :1;
    IO_BYTE _ID3 :1;
    IO_BYTE _ID4 :1;
    IO_BYTE _ID5 :1;
    IO_BYTE _ID6 :1;
    IO_BYTE _ID7 :1;
  }bit;
 }IF2ARB1L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ID8 :1;
    IO_BYTE _ID9 :1;
    IO_BYTE _ID10 :1;
    IO_BYTE _ID11 :1;
    IO_BYTE _ID12 :1;
    IO_BYTE _ID13 :1;
    IO_BYTE _ID14 :1;
    IO_BYTE _ID15 :1;
  }bit;
 }IF2ARB1H0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _ID16 :1;
    IO_WORD _ID17 :1;
    IO_WORD _ID18 :1;
    IO_WORD _ID19 :1;
    IO_WORD _ID20 :1;
    IO_WORD _ID21 :1;
    IO_WORD _ID22 :1;
    IO_WORD _ID23 :1;
    IO_WORD _ID24 :1;
    IO_WORD _ID25 :1;
    IO_WORD _ID26 :1;
    IO_WORD _ID27 :1;
    IO_WORD _ID28 :1;
    IO_WORD _DIR :1;
    IO_WORD _XTD :1;
    IO_WORD _MSGVAL :1;
  }bit;
 }IF2ARB20STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ID16 :1;
    IO_BYTE _ID17 :1;
    IO_BYTE _ID18 :1;
    IO_BYTE _ID19 :1;
    IO_BYTE _ID20 :1;
    IO_BYTE _ID21 :1;
    IO_BYTE _ID22 :1;
    IO_BYTE _ID23 :1;
  }bit;
 }IF2ARB2L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ID24 :1;
    IO_BYTE _ID25 :1;
    IO_BYTE _ID26 :1;
    IO_BYTE _ID27 :1;
    IO_BYTE _ID28 :1;
    IO_BYTE _DIR :1;
    IO_BYTE _XTD :1;
    IO_BYTE _MSGVAL :1;
  }bit;
 }IF2ARB2H0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _DLC0 :1;
    IO_WORD _DLC1 :1;
    IO_WORD _DLC2 :1;
    IO_WORD _DLC3 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _EOB :1;
    IO_WORD _TXRQST :1;
    IO_WORD _RMTEN :1;
    IO_WORD _RXIE :1;
    IO_WORD _TXIE :1;
    IO_WORD _UMASK :1;
    IO_WORD _INTPND :1;
    IO_WORD _MSGLST :1;
    IO_WORD _NEWDAT :1;
  }bit;
  struct{
    IO_WORD _DLC :4;
  }bitc;
 }IF2MCTR0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _DLC0 :1;
    IO_BYTE _DLC1 :1;
    IO_BYTE _DLC2 :1;
    IO_BYTE _DLC3 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _EOB :1;
  }bit;
  struct{
    IO_BYTE _DLC :4;
  }bitc;
 }IF2MCTRL0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TXRQST :1;
    IO_BYTE _RMTEN :1;
    IO_BYTE _RXIE :1;
    IO_BYTE _TXIE :1;
    IO_BYTE _UMASK :1;
    IO_BYTE _INTPND :1;
    IO_BYTE _MSGLST :1;
    IO_BYTE _NEWDAT :1;
  }bit;
 }IF2MCTRH0STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
  }bit;
 }IF2DTA0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF2DTA10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF2DTA1L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF2DTA1H0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF2DTA20STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF2DTA2L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF2DTA2H0STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
  }bit;
 }IF2DTB0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF2DTB10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF2DTB1L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF2DTB1H0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF2DTB20STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF2DTB2L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF2DTB2H0STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD _TXRQST1 :1;
    IO_LWORD _TXRQST2 :1;
    IO_LWORD _TXRQST3 :1;
    IO_LWORD _TXRQST4 :1;
    IO_LWORD _TXRQST5 :1;
    IO_LWORD _TXRQST6 :1;
    IO_LWORD _TXRQST7 :1;
    IO_LWORD _TXRQST8 :1;
    IO_LWORD _TXRQST9 :1;
    IO_LWORD _TXRQST10 :1;
    IO_LWORD _TXRQST11 :1;
    IO_LWORD _TXRQST12 :1;
    IO_LWORD _TXRQST13 :1;
    IO_LWORD _TXRQST14 :1;
    IO_LWORD _TXRQST15 :1;
    IO_LWORD _TXRQST16 :1;
    IO_LWORD _TXRQST17 :1;
    IO_LWORD _TXRQST18 :1;
    IO_LWORD _TXRQST19 :1;
    IO_LWORD _TXRQST20 :1;
    IO_LWORD _TXRQST21 :1;
    IO_LWORD _TXRQST22 :1;
    IO_LWORD _TXRQST23 :1;
    IO_LWORD _TXRQST24 :1;
    IO_LWORD _TXRQST25 :1;
    IO_LWORD _TXRQST26 :1;
    IO_LWORD _TXRQST27 :1;
    IO_LWORD _TXRQST28 :1;
    IO_LWORD _TXRQST29 :1;
    IO_LWORD _TXRQST30 :1;
    IO_LWORD _TXRQST31 :1;
    IO_LWORD _TXRQST32 :1;
  }bit;
  struct{
    IO_LWORD _TXRQST :32;
  }bitc;
 }TREQR0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TXRQST1 :1;
    IO_WORD _TXRQST2 :1;
    IO_WORD _TXRQST3 :1;
    IO_WORD _TXRQST4 :1;
    IO_WORD _TXRQST5 :1;
    IO_WORD _TXRQST6 :1;
    IO_WORD _TXRQST7 :1;
    IO_WORD _TXRQST8 :1;
    IO_WORD _TXRQST9 :1;
    IO_WORD _TXRQST10 :1;
    IO_WORD _TXRQST11 :1;
    IO_WORD _TXRQST12 :1;
    IO_WORD _TXRQST13 :1;
    IO_WORD _TXRQST14 :1;
    IO_WORD _TXRQST15 :1;
    IO_WORD _TXRQST16 :1;
  }bit;
 }TREQR10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TXRQST1 :1;
    IO_BYTE _TXRQST2 :1;
    IO_BYTE _TXRQST3 :1;
    IO_BYTE _TXRQST4 :1;
    IO_BYTE _TXRQST5 :1;
    IO_BYTE _TXRQST6 :1;
    IO_BYTE _TXRQST7 :1;
    IO_BYTE _TXRQST8 :1;
  }bit;
 }TREQR1L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TXRQST9 :1;
    IO_BYTE _TXRQST10 :1;
    IO_BYTE _TXRQST11 :1;
    IO_BYTE _TXRQST12 :1;
    IO_BYTE _TXRQST13 :1;
    IO_BYTE _TXRQST14 :1;
    IO_BYTE _TXRQST15 :1;
    IO_BYTE _TXRQST16 :1;
  }bit;
 }TREQR1H0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TXRQST17 :1;
    IO_WORD _TXRQST18 :1;
    IO_WORD _TXRQST19 :1;
    IO_WORD _TXRQST20 :1;
    IO_WORD _TXRQST21 :1;
    IO_WORD _TXRQST22 :1;
    IO_WORD _TXRQST23 :1;
    IO_WORD _TXRQST24 :1;
    IO_WORD _TXRQST25 :1;
    IO_WORD _TXRQST26 :1;
    IO_WORD _TXRQST27 :1;
    IO_WORD _TXRQST28 :1;
    IO_WORD _TXRQST29 :1;
    IO_WORD _TXRQST30 :1;
    IO_WORD _TXRQST31 :1;
    IO_WORD _TXRQST32 :1;
  }bit;
 }TREQR20STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TXRQST17 :1;
    IO_BYTE _TXRQST18 :1;
    IO_BYTE _TXRQST19 :1;
    IO_BYTE _TXRQST20 :1;
    IO_BYTE _TXRQST21 :1;
    IO_BYTE _TXRQST22 :1;
    IO_BYTE _TXRQST23 :1;
    IO_BYTE _TXRQST24 :1;
  }bit;
 }TREQR2L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TXRQST25 :1;
    IO_BYTE _TXRQST26 :1;
    IO_BYTE _TXRQST27 :1;
    IO_BYTE _TXRQST28 :1;
    IO_BYTE _TXRQST29 :1;
    IO_BYTE _TXRQST30 :1;
    IO_BYTE _TXRQST31 :1;
    IO_BYTE _TXRQST32 :1;
  }bit;
 }TREQR2H0STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD _NEWDAT1 :1;
    IO_LWORD _NEWDAT2 :1;
    IO_LWORD _NEWDAT3 :1;
    IO_LWORD _NEWDAT4 :1;
    IO_LWORD _NEWDAT5 :1;
    IO_LWORD _NEWDAT6 :1;
    IO_LWORD _NEWDAT7 :1;
    IO_LWORD _NEWDAT8 :1;
    IO_LWORD _NEWDAT9 :1;
    IO_LWORD _NEWDAT10 :1;
    IO_LWORD _NEWDAT11 :1;
    IO_LWORD _NEWDAT12 :1;
    IO_LWORD _NEWDAT13 :1;
    IO_LWORD _NEWDAT14 :1;
    IO_LWORD _NEWDAT15 :1;
    IO_LWORD _NEWDAT16 :1;
    IO_LWORD _NEWDAT17 :1;
    IO_LWORD _NEWDAT18 :1;
    IO_LWORD _NEWDAT19 :1;
    IO_LWORD _NEWDAT20 :1;
    IO_LWORD _NEWDAT21 :1;
    IO_LWORD _NEWDAT22 :1;
    IO_LWORD _NEWDAT23 :1;
    IO_LWORD _NEWDAT24 :1;
    IO_LWORD _NEWDAT25 :1;
    IO_LWORD _NEWDAT26 :1;
    IO_LWORD _NEWDAT27 :1;
    IO_LWORD _NEWDAT28 :1;
    IO_LWORD _NEWDAT29 :1;
    IO_LWORD _NEWDAT30 :1;
    IO_LWORD _NEWDAT31 :1;
    IO_LWORD _NEWDAT32 :1;
  }bit;
  struct{
    IO_LWORD _NEWDAT :32;
  }bitc;
 }NEWDT0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _NEWDAT1 :1;
    IO_WORD _NEWDAT2 :1;
    IO_WORD _NEWDAT3 :1;
    IO_WORD _NEWDAT4 :1;
    IO_WORD _NEWDAT5 :1;
    IO_WORD _NEWDAT6 :1;
    IO_WORD _NEWDAT7 :1;
    IO_WORD _NEWDAT8 :1;
    IO_WORD _NEWDAT9 :1;
    IO_WORD _NEWDAT10 :1;
    IO_WORD _NEWDAT11 :1;
    IO_WORD _NEWDAT12 :1;
    IO_WORD _NEWDAT13 :1;
    IO_WORD _NEWDAT14 :1;
    IO_WORD _NEWDAT15 :1;
    IO_WORD _NEWDAT16 :1;
  }bit;
 }NEWDT10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _NEWDAT1 :1;
    IO_BYTE _NEWDAT2 :1;
    IO_BYTE _NEWDAT3 :1;
    IO_BYTE _NEWDAT4 :1;
    IO_BYTE _NEWDAT5 :1;
    IO_BYTE _NEWDAT6 :1;
    IO_BYTE _NEWDAT7 :1;
    IO_BYTE _NEWDAT8 :1;
  }bit;
 }NEWDT1L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _NEWDAT9 :1;
    IO_BYTE _NEWDAT10 :1;
    IO_BYTE _NEWDAT11 :1;
    IO_BYTE _NEWDAT12 :1;
    IO_BYTE _NEWDAT13 :1;
    IO_BYTE _NEWDAT14 :1;
    IO_BYTE _NEWDAT15 :1;
    IO_BYTE _NEWDAT16 :1;
  }bit;
 }NEWDT1H0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _NEWDAT17 :1;
    IO_WORD _NEWDAT18 :1;
    IO_WORD _NEWDAT19 :1;
    IO_WORD _NEWDAT20 :1;
    IO_WORD _NEWDAT21 :1;
    IO_WORD _NEWDAT22 :1;
    IO_WORD _NEWDAT23 :1;
    IO_WORD _NEWDAT24 :1;
    IO_WORD _NEWDAT25 :1;
    IO_WORD _NEWDAT26 :1;
    IO_WORD _NEWDAT27 :1;
    IO_WORD _NEWDAT28 :1;
    IO_WORD _NEWDAT29 :1;
    IO_WORD _NEWDAT30 :1;
    IO_WORD _NEWDAT31 :1;
    IO_WORD _NEWDAT32 :1;
  }bit;
 }NEWDT20STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _NEWDAT17 :1;
    IO_BYTE _NEWDAT18 :1;
    IO_BYTE _NEWDAT19 :1;
    IO_BYTE _NEWDAT20 :1;
    IO_BYTE _NEWDAT21 :1;
    IO_BYTE _NEWDAT22 :1;
    IO_BYTE _NEWDAT23 :1;
    IO_BYTE _NEWDAT24 :1;
  }bit;
 }NEWDT2L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _NEWDAT25 :1;
    IO_BYTE _NEWDAT26 :1;
    IO_BYTE _NEWDAT27 :1;
    IO_BYTE _NEWDAT28 :1;
    IO_BYTE _NEWDAT29 :1;
    IO_BYTE _NEWDAT30 :1;
    IO_BYTE _NEWDAT31 :1;
    IO_BYTE _NEWDAT32 :1;
  }bit;
 }NEWDT2H0STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD _INTPND1 :1;
    IO_LWORD _INTPND2 :1;
    IO_LWORD _INTPND3 :1;
    IO_LWORD _INTPND4 :1;
    IO_LWORD _INTPND5 :1;
    IO_LWORD _INTPND6 :1;
    IO_LWORD _INTPND7 :1;
    IO_LWORD _INTPND8 :1;
    IO_LWORD _INTPND9 :1;
    IO_LWORD _INTPND10 :1;
    IO_LWORD _INTPND11 :1;
    IO_LWORD _INTPND12 :1;
    IO_LWORD _INTPND13 :1;
    IO_LWORD _INTPND14 :1;
    IO_LWORD _INTPND15 :1;
    IO_LWORD _INTPND16 :1;
    IO_LWORD _INTPND17 :1;
    IO_LWORD _INTPND18 :1;
    IO_LWORD _INTPND19 :1;
    IO_LWORD _INTPND20 :1;
    IO_LWORD _INTPND21 :1;
    IO_LWORD _INTPND22 :1;
    IO_LWORD _INTPND23 :1;
    IO_LWORD _INTPND24 :1;
    IO_LWORD _INTPND25 :1;
    IO_LWORD _INTPND26 :1;
    IO_LWORD _INTPND27 :1;
    IO_LWORD _INTPND28 :1;
    IO_LWORD _INTPND29 :1;
    IO_LWORD _INTPND30 :1;
    IO_LWORD _INTPND31 :1;
    IO_LWORD _INTPND32 :1;
  }bit;
  struct{
    IO_LWORD _INTPND :32;
  }bitc;
 }INTPND0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _INTPND1 :1;
    IO_WORD _INTPND2 :1;
    IO_WORD _INTPND3 :1;
    IO_WORD _INTPND4 :1;
    IO_WORD _INTPND5 :1;
    IO_WORD _INTPND6 :1;
    IO_WORD _INTPND7 :1;
    IO_WORD _INTPND8 :1;
    IO_WORD _INTPND9 :1;
    IO_WORD _INTPND10 :1;
    IO_WORD _INTPND11 :1;
    IO_WORD _INTPND12 :1;
    IO_WORD _INTPND13 :1;
    IO_WORD _INTPND14 :1;
    IO_WORD _INTPND15 :1;
    IO_WORD _INTPND16 :1;
  }bit;
 }INTPND10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INTPND1 :1;
    IO_BYTE _INTPND2 :1;
    IO_BYTE _INTPND3 :1;
    IO_BYTE _INTPND4 :1;
    IO_BYTE _INTPND5 :1;
    IO_BYTE _INTPND6 :1;
    IO_BYTE _INTPND7 :1;
    IO_BYTE _INTPND8 :1;
  }bit;
 }INTPND1L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INTPND9 :1;
    IO_BYTE _INTPND10 :1;
    IO_BYTE _INTPND11 :1;
    IO_BYTE _INTPND12 :1;
    IO_BYTE _INTPND13 :1;
    IO_BYTE _INTPND14 :1;
    IO_BYTE _INTPND15 :1;
    IO_BYTE _INTPND16 :1;
  }bit;
 }INTPND1H0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _INTPND17 :1;
    IO_WORD _INTPND18 :1;
    IO_WORD _INTPND19 :1;
    IO_WORD _INTPND20 :1;
    IO_WORD _INTPND21 :1;
    IO_WORD _INTPND22 :1;
    IO_WORD _INTPND23 :1;
    IO_WORD _INTPND24 :1;
    IO_WORD _INTPND25 :1;
    IO_WORD _INTPND26 :1;
    IO_WORD _INTPND27 :1;
    IO_WORD _INTPND28 :1;
    IO_WORD _INTPND29 :1;
    IO_WORD _INTPND30 :1;
    IO_WORD _INTPND31 :1;
    IO_WORD _INTPND32 :1;
  }bit;
 }INTPND20STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INTPND17 :1;
    IO_BYTE _INTPND18 :1;
    IO_BYTE _INTPND19 :1;
    IO_BYTE _INTPND20 :1;
    IO_BYTE _INTPND21 :1;
    IO_BYTE _INTPND22 :1;
    IO_BYTE _INTPND23 :1;
    IO_BYTE _INTPND24 :1;
  }bit;
 }INTPND2L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INTPND25 :1;
    IO_BYTE _INTPND26 :1;
    IO_BYTE _INTPND27 :1;
    IO_BYTE _INTPND28 :1;
    IO_BYTE _INTPND29 :1;
    IO_BYTE _INTPND30 :1;
    IO_BYTE _INTPND31 :1;
    IO_BYTE _INTPND32 :1;
  }bit;
 }INTPND2H0STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD _MSGVAL1 :1;
    IO_LWORD _MSGVAL2 :1;
    IO_LWORD _MSGVAL3 :1;
    IO_LWORD _MSGVAL4 :1;
    IO_LWORD _MSGVAL5 :1;
    IO_LWORD _MSGVAL6 :1;
    IO_LWORD _MSGVAL7 :1;
    IO_LWORD _MSGVAL8 :1;
    IO_LWORD _MSGVAL9 :1;
    IO_LWORD _MSGVAL10 :1;
    IO_LWORD _MSGVAL11 :1;
    IO_LWORD _MSGVAL12 :1;
    IO_LWORD _MSGVAL13 :1;
    IO_LWORD _MSGVAL14 :1;
    IO_LWORD _MSGVAL15 :1;
    IO_LWORD _MSGVAL16 :1;
    IO_LWORD _MSGVAL17 :1;
    IO_LWORD _MSGVAL18 :1;
    IO_LWORD _MSGVAL19 :1;
    IO_LWORD _MSGVAL20 :1;
    IO_LWORD _MSGVAL21 :1;
    IO_LWORD _MSGVAL22 :1;
    IO_LWORD _MSGVAL23 :1;
    IO_LWORD _MSGVAL24 :1;
    IO_LWORD _MSGVAL25 :1;
    IO_LWORD _MSGVAL26 :1;
    IO_LWORD _MSGVAL27 :1;
    IO_LWORD _MSGVAL28 :1;
    IO_LWORD _MSGVAL29 :1;
    IO_LWORD _MSGVAL30 :1;
    IO_LWORD _MSGVAL31 :1;
    IO_LWORD _MSGVAL32 :1;
  }bit;
  struct{
    IO_LWORD _MSGVAL :32;
  }bitc;
 }MSGVAL0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _MSGVAL1 :1;
    IO_WORD _MSGVAL2 :1;
    IO_WORD _MSGVAL3 :1;
    IO_WORD _MSGVAL4 :1;
    IO_WORD _MSGVAL5 :1;
    IO_WORD _MSGVAL6 :1;
    IO_WORD _MSGVAL7 :1;
    IO_WORD _MSGVAL8 :1;
    IO_WORD _MSGVAL9 :1;
    IO_WORD _MSGVAL10 :1;
    IO_WORD _MSGVAL11 :1;
    IO_WORD _MSGVAL12 :1;
    IO_WORD _MSGVAL13 :1;
    IO_WORD _MSGVAL14 :1;
    IO_WORD _MSGVAL15 :1;
    IO_WORD _MSGVAL16 :1;
  }bit;
 }MSGVAL10STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSGVAL1 :1;
    IO_BYTE _MSGVAL2 :1;
    IO_BYTE _MSGVAL3 :1;
    IO_BYTE _MSGVAL4 :1;
    IO_BYTE _MSGVAL5 :1;
    IO_BYTE _MSGVAL6 :1;
    IO_BYTE _MSGVAL7 :1;
    IO_BYTE _MSGVAL8 :1;
  }bit;
 }MSGVAL1L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSGVAL9 :1;
    IO_BYTE _MSGVAL10 :1;
    IO_BYTE _MSGVAL11 :1;
    IO_BYTE _MSGVAL12 :1;
    IO_BYTE _MSGVAL13 :1;
    IO_BYTE _MSGVAL14 :1;
    IO_BYTE _MSGVAL15 :1;
    IO_BYTE _MSGVAL16 :1;
  }bit;
 }MSGVAL1H0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _MSGVAL17 :1;
    IO_WORD _MSGVAL18 :1;
    IO_WORD _MSGVAL19 :1;
    IO_WORD _MSGVAL20 :1;
    IO_WORD _MSGVAL21 :1;
    IO_WORD _MSGVAL22 :1;
    IO_WORD _MSGVAL23 :1;
    IO_WORD _MSGVAL24 :1;
    IO_WORD _MSGVAL25 :1;
    IO_WORD _MSGVAL26 :1;
    IO_WORD _MSGVAL27 :1;
    IO_WORD _MSGVAL28 :1;
    IO_WORD _MSGVAL29 :1;
    IO_WORD _MSGVAL30 :1;
    IO_WORD _MSGVAL31 :1;
    IO_WORD _MSGVAL32 :1;
  }bit;
 }MSGVAL20STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSGVAL17 :1;
    IO_BYTE _MSGVAL18 :1;
    IO_BYTE _MSGVAL19 :1;
    IO_BYTE _MSGVAL20 :1;
    IO_BYTE _MSGVAL21 :1;
    IO_BYTE _MSGVAL22 :1;
    IO_BYTE _MSGVAL23 :1;
    IO_BYTE _MSGVAL24 :1;
  }bit;
 }MSGVAL2L0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSGVAL25 :1;
    IO_BYTE _MSGVAL26 :1;
    IO_BYTE _MSGVAL27 :1;
    IO_BYTE _MSGVAL28 :1;
    IO_BYTE _MSGVAL29 :1;
    IO_BYTE _MSGVAL30 :1;
    IO_BYTE _MSGVAL31 :1;
    IO_BYTE _MSGVAL32 :1;
  }bit;
 }MSGVAL2H0STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OE :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }COER0STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _INIT :1;
    IO_WORD _IE :1;
    IO_WORD _SIE :1;
    IO_WORD _EIE :1;
    IO_WORD  :1;
    IO_WORD _DAR :1;
    IO_WORD _CCE :1;
    IO_WORD _TEST :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }CTRLR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INIT :1;
    IO_BYTE _IE :1;
    IO_BYTE _SIE :1;
    IO_BYTE _EIE :1;
    IO_BYTE  :1;
    IO_BYTE _DAR :1;
    IO_BYTE _CCE :1;
    IO_BYTE _TEST :1;
  }bit;
 }CTRLRL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }CTRLRH1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _LEC0 :1;
    IO_WORD _LEC1 :1;
    IO_WORD _LEC2 :1;
    IO_WORD _TXOK :1;
    IO_WORD _RXOK :1;
    IO_WORD _EPASS :1;
    IO_WORD _EWARN :1;
    IO_WORD _BOFF :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD _LEC :3;
  }bitc;
 }STATR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _LEC0 :1;
    IO_BYTE _LEC1 :1;
    IO_BYTE _LEC2 :1;
    IO_BYTE _TXOK :1;
    IO_BYTE _RXOK :1;
    IO_BYTE _EPASS :1;
    IO_BYTE _EWARN :1;
    IO_BYTE _BOFF :1;
  }bit;
  struct{
    IO_BYTE _LEC :3;
  }bitc;
 }STATRL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }STATRH1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TEC0 :1;
    IO_WORD _TEC1 :1;
    IO_WORD _TEC2 :1;
    IO_WORD _TEC3 :1;
    IO_WORD _TEC4 :1;
    IO_WORD _TEC5 :1;
    IO_WORD _TEC6 :1;
    IO_WORD _TEC7 :1;
    IO_WORD _REC0 :1;
    IO_WORD _REC1 :1;
    IO_WORD _REC2 :1;
    IO_WORD _REC3 :1;
    IO_WORD _REC4 :1;
    IO_WORD _REC5 :1;
    IO_WORD _REC6 :1;
    IO_WORD _RP :1;
  }bit;
  struct{
    IO_WORD _TEC :8;
    IO_WORD _REC :7;
  }bitc;
 }ERRCNT1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TEC0 :1;
    IO_BYTE _TEC1 :1;
    IO_BYTE _TEC2 :1;
    IO_BYTE _TEC3 :1;
    IO_BYTE _TEC4 :1;
    IO_BYTE _TEC5 :1;
    IO_BYTE _TEC6 :1;
    IO_BYTE _TEC7 :1;
  }bit;
  struct{
    IO_BYTE _TEC :8;
  }bitc;
 }ERRCNTL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _REC0 :1;
    IO_BYTE _REC1 :1;
    IO_BYTE _REC2 :1;
    IO_BYTE _REC3 :1;
    IO_BYTE _REC4 :1;
    IO_BYTE _REC5 :1;
    IO_BYTE _REC6 :1;
    IO_BYTE _RP :1;
  }bit;
  struct{
    IO_BYTE _REC :7;
  }bitc;
 }ERRCNTH1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _BRP0 :1;
    IO_WORD _BRP1 :1;
    IO_WORD _BRP2 :1;
    IO_WORD _BRP3 :1;
    IO_WORD _BRP4 :1;
    IO_WORD _BRP5 :1;
    IO_WORD _SJW0 :1;
    IO_WORD _SJW1 :1;
    IO_WORD _TSEG10 :1;
    IO_WORD _TSEG11 :1;
    IO_WORD _TSEG12 :1;
    IO_WORD _TSEG13 :1;
    IO_WORD _TSEG20 :1;
    IO_WORD _TSEG21 :1;
    IO_WORD _TSEG22 :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD _BRP :6;
    IO_WORD _SJW :2;
    IO_WORD _TSEG1 :4;
    IO_WORD _TSEG2 :3;
  }bitc;
 }BTR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _BRP0 :1;
    IO_BYTE _BRP1 :1;
    IO_BYTE _BRP2 :1;
    IO_BYTE _BRP3 :1;
    IO_BYTE _BRP4 :1;
    IO_BYTE _BRP5 :1;
    IO_BYTE _SJW0 :1;
    IO_BYTE _SJW1 :1;
  }bit;
  struct{
    IO_BYTE _BRP :6;
    IO_BYTE _SJW :2;
  }bitc;
 }BTRL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TSEG10 :1;
    IO_BYTE _TSEG11 :1;
    IO_BYTE _TSEG12 :1;
    IO_BYTE _TSEG13 :1;
    IO_BYTE _TSEG20 :1;
    IO_BYTE _TSEG21 :1;
    IO_BYTE _TSEG22 :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _TSEG1 :4;
    IO_BYTE _TSEG2 :3;
  }bitc;
 }BTRH1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _INTID0 :1;
    IO_WORD _INTID1 :1;
    IO_WORD _INTID2 :1;
    IO_WORD _INTID3 :1;
    IO_WORD _INTID4 :1;
    IO_WORD _INTID5 :1;
    IO_WORD _INTID6 :1;
    IO_WORD _INTID7 :1;
    IO_WORD _INTID8 :1;
    IO_WORD _INTID9 :1;
    IO_WORD _INTID10 :1;
    IO_WORD _INTID11 :1;
    IO_WORD _INTID12 :1;
    IO_WORD _INTID13 :1;
    IO_WORD _INTID14 :1;
    IO_WORD _INTID15 :1;
  }bit;
  struct{
    IO_WORD _INTID :16;
  }bitc;
 }INTR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INTID0 :1;
    IO_BYTE _INTID1 :1;
    IO_BYTE _INTID2 :1;
    IO_BYTE _INTID3 :1;
    IO_BYTE _INTID4 :1;
    IO_BYTE _INTID5 :1;
    IO_BYTE _INTID6 :1;
    IO_BYTE _INTID7 :1;
  }bit;
 }INTRL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INTID8 :1;
    IO_BYTE _INTID9 :1;
    IO_BYTE _INTID10 :1;
    IO_BYTE _INTID11 :1;
    IO_BYTE _INTID12 :1;
    IO_BYTE _INTID13 :1;
    IO_BYTE _INTID14 :1;
    IO_BYTE _INTID15 :1;
  }bit;
 }INTRH1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _BASIC :1;
    IO_WORD _SILENT :1;
    IO_WORD _LBACK :1;
    IO_WORD _TX0 :1;
    IO_WORD _TX1 :1;
    IO_WORD _RX :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }TESTR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _BASIC :1;
    IO_BYTE _SILENT :1;
    IO_BYTE _LBACK :1;
    IO_BYTE _TX0 :1;
    IO_BYTE _TX1 :1;
    IO_BYTE _RX :1;
  }bit;
 }TESTRL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }TESTRH1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _BRPE0 :1;
    IO_WORD _BRPE1 :1;
    IO_WORD _BRPE2 :1;
    IO_WORD _BRPE3 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
  struct{
    IO_WORD _BRPE :4;
  }bitc;
 }BRPER1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _BRPE0 :1;
    IO_BYTE _BRPE1 :1;
    IO_BYTE _BRPE2 :1;
    IO_BYTE _BRPE3 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
  struct{
    IO_BYTE _BRPE :4;
  }bitc;
 }BRPERL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }BRPERH1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _MSGN0 :1;
    IO_WORD _MSGN1 :1;
    IO_WORD _MSGN2 :1;
    IO_WORD _MSGN3 :1;
    IO_WORD _MSGN4 :1;
    IO_WORD _MSGN5 :1;
    IO_WORD _MSGN6 :1;
    IO_WORD _MSGN7 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _BUSY :1;
  }bit;
 }IF1CREQ1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSGN0 :1;
    IO_BYTE _MSGN1 :1;
    IO_BYTE _MSGN2 :1;
    IO_BYTE _MSGN3 :1;
    IO_BYTE _MSGN4 :1;
    IO_BYTE _MSGN5 :1;
    IO_BYTE _MSGN6 :1;
    IO_BYTE _MSGN7 :1;
  }bit;
 }IF1CREQL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _BUSY :1;
  }bit;
 }IF1CREQH1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _DATAB :1;
    IO_WORD _DATAA :1;
    IO_WORD _TXREQ :1;
    IO_WORD _CIP :1;
    IO_WORD _CONTROL :1;
    IO_WORD _ARB :1;
    IO_WORD _MASK :1;
    IO_WORD _WRRD :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF1CMSK1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _DATAB :1;
    IO_BYTE _DATAA :1;
    IO_BYTE _TXREQ :1;
    IO_BYTE _CIP :1;
    IO_BYTE _CONTROL :1;
    IO_BYTE _ARB :1;
    IO_BYTE _MASK :1;
    IO_BYTE _WRRD :1;
  }bit;
 }IF1CMSKL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF1CMSKH1STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD _MSK0 :1;
    IO_LWORD _MSK1 :1;
    IO_LWORD _MSK2 :1;
    IO_LWORD _MSK3 :1;
    IO_LWORD _MSK4 :1;
    IO_LWORD _MSK5 :1;
    IO_LWORD _MSK6 :1;
    IO_LWORD _MSK7 :1;
    IO_LWORD _MSK8 :1;
    IO_LWORD _MSK9 :1;
    IO_LWORD _MSK10 :1;
    IO_LWORD _MSK11 :1;
    IO_LWORD _MSK12 :1;
    IO_LWORD _MSK13 :1;
    IO_LWORD _MSK14 :1;
    IO_LWORD _MSK15 :1;
    IO_LWORD _MSK16 :1;
    IO_LWORD _MSK17 :1;
    IO_LWORD _MSK18 :1;
    IO_LWORD _MSK19 :1;
    IO_LWORD _MSK20 :1;
    IO_LWORD _MSK21 :1;
    IO_LWORD _MSK22 :1;
    IO_LWORD _MSK23 :1;
    IO_LWORD _MSK24 :1;
    IO_LWORD _MSK25 :1;
    IO_LWORD _MSK26 :1;
    IO_LWORD _MSK27 :1;
    IO_LWORD _MSK28 :1;
    IO_LWORD  :1;
    IO_LWORD _MDIR :1;
    IO_LWORD _MXTD :1;
  }bit;
  struct{
    IO_LWORD _MSK :29;
  }bitc;
 }IF1MSK1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _MSK0 :1;
    IO_WORD _MSK1 :1;
    IO_WORD _MSK2 :1;
    IO_WORD _MSK3 :1;
    IO_WORD _MSK4 :1;
    IO_WORD _MSK5 :1;
    IO_WORD _MSK6 :1;
    IO_WORD _MSK7 :1;
    IO_WORD _MSK8 :1;
    IO_WORD _MSK9 :1;
    IO_WORD _MSK10 :1;
    IO_WORD _MSK11 :1;
    IO_WORD _MSK12 :1;
    IO_WORD _MSK13 :1;
    IO_WORD _MSK14 :1;
    IO_WORD _MSK15 :1;
  }bit;
 }IF1MSK11STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSK0 :1;
    IO_BYTE _MSK1 :1;
    IO_BYTE _MSK2 :1;
    IO_BYTE _MSK3 :1;
    IO_BYTE _MSK4 :1;
    IO_BYTE _MSK5 :1;
    IO_BYTE _MSK6 :1;
    IO_BYTE _MSK7 :1;
  }bit;
 }IF1MSK1L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSK8 :1;
    IO_BYTE _MSK9 :1;
    IO_BYTE _MSK10 :1;
    IO_BYTE _MSK11 :1;
    IO_BYTE _MSK12 :1;
    IO_BYTE _MSK13 :1;
    IO_BYTE _MSK14 :1;
    IO_BYTE _MSK15 :1;
  }bit;
 }IF1MSK1H1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _MSK16 :1;
    IO_WORD _MSK17 :1;
    IO_WORD _MSK18 :1;
    IO_WORD _MSK19 :1;
    IO_WORD _MSK20 :1;
    IO_WORD _MSK21 :1;
    IO_WORD _MSK22 :1;
    IO_WORD _MSK23 :1;
    IO_WORD _MSK24 :1;
    IO_WORD _MSK25 :1;
    IO_WORD _MSK26 :1;
    IO_WORD _MSK27 :1;
    IO_WORD _MSK28 :1;
    IO_WORD  :1;
    IO_WORD _MDIR :1;
    IO_WORD _MXTD :1;
  }bit;
 }IF1MSK21STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSK16 :1;
    IO_BYTE _MSK17 :1;
    IO_BYTE _MSK18 :1;
    IO_BYTE _MSK19 :1;
    IO_BYTE _MSK20 :1;
    IO_BYTE _MSK21 :1;
    IO_BYTE _MSK22 :1;
    IO_BYTE _MSK23 :1;
  }bit;
 }IF1MSK2L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSK24 :1;
    IO_BYTE _MSK25 :1;
    IO_BYTE _MSK26 :1;
    IO_BYTE _MSK27 :1;
    IO_BYTE _MSK28 :1;
    IO_BYTE  :1;
    IO_BYTE _MDIR :1;
    IO_BYTE _MXTD :1;
  }bit;
 }IF1MSK2H1STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD _ID0 :1;
    IO_LWORD _ID1 :1;
    IO_LWORD _ID2 :1;
    IO_LWORD _ID3 :1;
    IO_LWORD _ID4 :1;
    IO_LWORD _ID5 :1;
    IO_LWORD _ID6 :1;
    IO_LWORD _ID7 :1;
    IO_LWORD _ID8 :1;
    IO_LWORD _ID9 :1;
    IO_LWORD _ID10 :1;
    IO_LWORD _ID11 :1;
    IO_LWORD _ID12 :1;
    IO_LWORD _ID13 :1;
    IO_LWORD _ID14 :1;
    IO_LWORD _ID15 :1;
    IO_LWORD _ID16 :1;
    IO_LWORD _ID17 :1;
    IO_LWORD _ID18 :1;
    IO_LWORD _ID19 :1;
    IO_LWORD _ID20 :1;
    IO_LWORD _ID21 :1;
    IO_LWORD _ID22 :1;
    IO_LWORD _ID23 :1;
    IO_LWORD _ID24 :1;
    IO_LWORD _ID25 :1;
    IO_LWORD _ID26 :1;
    IO_LWORD _ID27 :1;
    IO_LWORD _ID28 :1;
    IO_LWORD _DIR :1;
    IO_LWORD _XTD :1;
    IO_LWORD _MSGVAL :1;
  }bit;
  struct{
    IO_LWORD _ID :29;
  }bitc;
 }IF1ARB1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _ID0 :1;
    IO_WORD _ID1 :1;
    IO_WORD _ID2 :1;
    IO_WORD _ID3 :1;
    IO_WORD _ID4 :1;
    IO_WORD _ID5 :1;
    IO_WORD _ID6 :1;
    IO_WORD _ID7 :1;
    IO_WORD _ID8 :1;
    IO_WORD _ID9 :1;
    IO_WORD _ID10 :1;
    IO_WORD _ID11 :1;
    IO_WORD _ID12 :1;
    IO_WORD _ID13 :1;
    IO_WORD _ID14 :1;
    IO_WORD _ID15 :1;
  }bit;
 }IF1ARB11STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ID0 :1;
    IO_BYTE _ID1 :1;
    IO_BYTE _ID2 :1;
    IO_BYTE _ID3 :1;
    IO_BYTE _ID4 :1;
    IO_BYTE _ID5 :1;
    IO_BYTE _ID6 :1;
    IO_BYTE _ID7 :1;
  }bit;
 }IF1ARB1L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ID8 :1;
    IO_BYTE _ID9 :1;
    IO_BYTE _ID10 :1;
    IO_BYTE _ID11 :1;
    IO_BYTE _ID12 :1;
    IO_BYTE _ID13 :1;
    IO_BYTE _ID14 :1;
    IO_BYTE _ID15 :1;
  }bit;
 }IF1ARB1H1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _ID16 :1;
    IO_WORD _ID17 :1;
    IO_WORD _ID18 :1;
    IO_WORD _ID19 :1;
    IO_WORD _ID20 :1;
    IO_WORD _ID21 :1;
    IO_WORD _ID22 :1;
    IO_WORD _ID23 :1;
    IO_WORD _ID24 :1;
    IO_WORD _ID25 :1;
    IO_WORD _ID26 :1;
    IO_WORD _ID27 :1;
    IO_WORD _ID28 :1;
    IO_WORD _DIR :1;
    IO_WORD _XTD :1;
    IO_WORD _MSGVAL :1;
  }bit;
 }IF1ARB21STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ID16 :1;
    IO_BYTE _ID17 :1;
    IO_BYTE _ID18 :1;
    IO_BYTE _ID19 :1;
    IO_BYTE _ID20 :1;
    IO_BYTE _ID21 :1;
    IO_BYTE _ID22 :1;
    IO_BYTE _ID23 :1;
  }bit;
 }IF1ARB2L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ID24 :1;
    IO_BYTE _ID25 :1;
    IO_BYTE _ID26 :1;
    IO_BYTE _ID27 :1;
    IO_BYTE _ID28 :1;
    IO_BYTE _DIR :1;
    IO_BYTE _XTD :1;
    IO_BYTE _MSGVAL :1;
  }bit;
 }IF1ARB2H1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _DLC0 :1;
    IO_WORD _DLC1 :1;
    IO_WORD _DLC2 :1;
    IO_WORD _DLC3 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _EOB :1;
    IO_WORD _TXRQST :1;
    IO_WORD _RMTEN :1;
    IO_WORD _RXIE :1;
    IO_WORD _TXIE :1;
    IO_WORD _UMASK :1;
    IO_WORD _INTPND :1;
    IO_WORD _MSGLST :1;
    IO_WORD _NEWDAT :1;
  }bit;
  struct{
    IO_WORD _DLC :4;
  }bitc;
 }IF1MCTR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _DLC0 :1;
    IO_BYTE _DLC1 :1;
    IO_BYTE _DLC2 :1;
    IO_BYTE _DLC3 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _EOB :1;
  }bit;
  struct{
    IO_BYTE _DLC :4;
  }bitc;
 }IF1MCTRL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TXRQST :1;
    IO_BYTE _RMTEN :1;
    IO_BYTE _RXIE :1;
    IO_BYTE _TXIE :1;
    IO_BYTE _UMASK :1;
    IO_BYTE _INTPND :1;
    IO_BYTE _MSGLST :1;
    IO_BYTE _NEWDAT :1;
  }bit;
 }IF1MCTRH1STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
  }bit;
 }IF1DTA1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF1DTA11STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF1DTA1L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF1DTA1H1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF1DTA21STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF1DTA2L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF1DTA2H1STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
  }bit;
 }IF1DTB1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF1DTB11STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF1DTB1L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF1DTB1H1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF1DTB21STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF1DTB2L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF1DTB2H1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _MSGN0 :1;
    IO_WORD _MSGN1 :1;
    IO_WORD _MSGN2 :1;
    IO_WORD _MSGN3 :1;
    IO_WORD _MSGN4 :1;
    IO_WORD _MSGN5 :1;
    IO_WORD _MSGN6 :1;
    IO_WORD _MSGN7 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _BUSY :1;
  }bit;
 }IF2CREQ1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSGN0 :1;
    IO_BYTE _MSGN1 :1;
    IO_BYTE _MSGN2 :1;
    IO_BYTE _MSGN3 :1;
    IO_BYTE _MSGN4 :1;
    IO_BYTE _MSGN5 :1;
    IO_BYTE _MSGN6 :1;
    IO_BYTE _MSGN7 :1;
  }bit;
 }IF2CREQL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _BUSY :1;
  }bit;
 }IF2CREQH1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _DATAB :1;
    IO_WORD _DATAA :1;
    IO_WORD _TXREQ :1;
    IO_WORD _CIP :1;
    IO_WORD _CONTROL :1;
    IO_WORD _ARB :1;
    IO_WORD _MASK :1;
    IO_WORD _WRRD :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF2CMSK1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _DATAB :1;
    IO_BYTE _DATAA :1;
    IO_BYTE _TXREQ :1;
    IO_BYTE _CIP :1;
    IO_BYTE _CONTROL :1;
    IO_BYTE _ARB :1;
    IO_BYTE _MASK :1;
    IO_BYTE _WRRD :1;
  }bit;
 }IF2CMSKL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF2CMSKH1STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD _MSK0 :1;
    IO_LWORD _MSK1 :1;
    IO_LWORD _MSK2 :1;
    IO_LWORD _MSK3 :1;
    IO_LWORD _MSK4 :1;
    IO_LWORD _MSK5 :1;
    IO_LWORD _MSK6 :1;
    IO_LWORD _MSK7 :1;
    IO_LWORD _MSK8 :1;
    IO_LWORD _MSK9 :1;
    IO_LWORD _MSK10 :1;
    IO_LWORD _MSK11 :1;
    IO_LWORD _MSK12 :1;
    IO_LWORD _MSK13 :1;
    IO_LWORD _MSK14 :1;
    IO_LWORD _MSK15 :1;
    IO_LWORD _MSK16 :1;
    IO_LWORD _MSK17 :1;
    IO_LWORD _MSK18 :1;
    IO_LWORD _MSK19 :1;
    IO_LWORD _MSK20 :1;
    IO_LWORD _MSK21 :1;
    IO_LWORD _MSK22 :1;
    IO_LWORD _MSK23 :1;
    IO_LWORD _MSK24 :1;
    IO_LWORD _MSK25 :1;
    IO_LWORD _MSK26 :1;
    IO_LWORD _MSK27 :1;
    IO_LWORD _MSK28 :1;
    IO_LWORD  :1;
    IO_LWORD _MDIR :1;
    IO_LWORD _MXTD :1;
  }bit;
  struct{
    IO_LWORD _MSK :29;
  }bitc;
 }IF2MSK1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _MSK0 :1;
    IO_WORD _MSK1 :1;
    IO_WORD _MSK2 :1;
    IO_WORD _MSK3 :1;
    IO_WORD _MSK4 :1;
    IO_WORD _MSK5 :1;
    IO_WORD _MSK6 :1;
    IO_WORD _MSK7 :1;
    IO_WORD _MSK8 :1;
    IO_WORD _MSK9 :1;
    IO_WORD _MSK10 :1;
    IO_WORD _MSK11 :1;
    IO_WORD _MSK12 :1;
    IO_WORD _MSK13 :1;
    IO_WORD _MSK14 :1;
    IO_WORD _MSK15 :1;
  }bit;
 }IF2MSK11STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSK0 :1;
    IO_BYTE _MSK1 :1;
    IO_BYTE _MSK2 :1;
    IO_BYTE _MSK3 :1;
    IO_BYTE _MSK4 :1;
    IO_BYTE _MSK5 :1;
    IO_BYTE _MSK6 :1;
    IO_BYTE _MSK7 :1;
  }bit;
 }IF2MSK1L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSK8 :1;
    IO_BYTE _MSK9 :1;
    IO_BYTE _MSK10 :1;
    IO_BYTE _MSK11 :1;
    IO_BYTE _MSK12 :1;
    IO_BYTE _MSK13 :1;
    IO_BYTE _MSK14 :1;
    IO_BYTE _MSK15 :1;
  }bit;
 }IF2MSK1H1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _MSK16 :1;
    IO_WORD _MSK17 :1;
    IO_WORD _MSK18 :1;
    IO_WORD _MSK19 :1;
    IO_WORD _MSK20 :1;
    IO_WORD _MSK21 :1;
    IO_WORD _MSK22 :1;
    IO_WORD _MSK23 :1;
    IO_WORD _MSK24 :1;
    IO_WORD _MSK25 :1;
    IO_WORD _MSK26 :1;
    IO_WORD _MSK27 :1;
    IO_WORD _MSK28 :1;
    IO_WORD  :1;
    IO_WORD _MDIR :1;
    IO_WORD _MXTD :1;
  }bit;
 }IF2MSK21STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSK16 :1;
    IO_BYTE _MSK17 :1;
    IO_BYTE _MSK18 :1;
    IO_BYTE _MSK19 :1;
    IO_BYTE _MSK20 :1;
    IO_BYTE _MSK21 :1;
    IO_BYTE _MSK22 :1;
    IO_BYTE _MSK23 :1;
  }bit;
 }IF2MSK2L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSK24 :1;
    IO_BYTE _MSK25 :1;
    IO_BYTE _MSK26 :1;
    IO_BYTE _MSK27 :1;
    IO_BYTE _MSK28 :1;
    IO_BYTE  :1;
    IO_BYTE _MDIR :1;
    IO_BYTE _MXTD :1;
  }bit;
 }IF2MSK2H1STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD _ID0 :1;
    IO_LWORD _ID1 :1;
    IO_LWORD _ID2 :1;
    IO_LWORD _ID3 :1;
    IO_LWORD _ID4 :1;
    IO_LWORD _ID5 :1;
    IO_LWORD _ID6 :1;
    IO_LWORD _ID7 :1;
    IO_LWORD _ID8 :1;
    IO_LWORD _ID9 :1;
    IO_LWORD _ID10 :1;
    IO_LWORD _ID11 :1;
    IO_LWORD _ID12 :1;
    IO_LWORD _ID13 :1;
    IO_LWORD _ID14 :1;
    IO_LWORD _ID15 :1;
    IO_LWORD _ID16 :1;
    IO_LWORD _ID17 :1;
    IO_LWORD _ID18 :1;
    IO_LWORD _ID19 :1;
    IO_LWORD _ID20 :1;
    IO_LWORD _ID21 :1;
    IO_LWORD _ID22 :1;
    IO_LWORD _ID23 :1;
    IO_LWORD _ID24 :1;
    IO_LWORD _ID25 :1;
    IO_LWORD _ID26 :1;
    IO_LWORD _ID27 :1;
    IO_LWORD _ID28 :1;
    IO_LWORD _DIR :1;
    IO_LWORD _XTD :1;
    IO_LWORD _MSGVAL :1;
  }bit;
  struct{
    IO_LWORD _ID :29;
  }bitc;
 }IF2ARB1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _ID0 :1;
    IO_WORD _ID1 :1;
    IO_WORD _ID2 :1;
    IO_WORD _ID3 :1;
    IO_WORD _ID4 :1;
    IO_WORD _ID5 :1;
    IO_WORD _ID6 :1;
    IO_WORD _ID7 :1;
    IO_WORD _ID8 :1;
    IO_WORD _ID9 :1;
    IO_WORD _ID10 :1;
    IO_WORD _ID11 :1;
    IO_WORD _ID12 :1;
    IO_WORD _ID13 :1;
    IO_WORD _ID14 :1;
    IO_WORD _ID15 :1;
  }bit;
 }IF2ARB11STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ID0 :1;
    IO_BYTE _ID1 :1;
    IO_BYTE _ID2 :1;
    IO_BYTE _ID3 :1;
    IO_BYTE _ID4 :1;
    IO_BYTE _ID5 :1;
    IO_BYTE _ID6 :1;
    IO_BYTE _ID7 :1;
  }bit;
 }IF2ARB1L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ID8 :1;
    IO_BYTE _ID9 :1;
    IO_BYTE _ID10 :1;
    IO_BYTE _ID11 :1;
    IO_BYTE _ID12 :1;
    IO_BYTE _ID13 :1;
    IO_BYTE _ID14 :1;
    IO_BYTE _ID15 :1;
  }bit;
 }IF2ARB1H1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _ID16 :1;
    IO_WORD _ID17 :1;
    IO_WORD _ID18 :1;
    IO_WORD _ID19 :1;
    IO_WORD _ID20 :1;
    IO_WORD _ID21 :1;
    IO_WORD _ID22 :1;
    IO_WORD _ID23 :1;
    IO_WORD _ID24 :1;
    IO_WORD _ID25 :1;
    IO_WORD _ID26 :1;
    IO_WORD _ID27 :1;
    IO_WORD _ID28 :1;
    IO_WORD _DIR :1;
    IO_WORD _XTD :1;
    IO_WORD _MSGVAL :1;
  }bit;
 }IF2ARB21STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ID16 :1;
    IO_BYTE _ID17 :1;
    IO_BYTE _ID18 :1;
    IO_BYTE _ID19 :1;
    IO_BYTE _ID20 :1;
    IO_BYTE _ID21 :1;
    IO_BYTE _ID22 :1;
    IO_BYTE _ID23 :1;
  }bit;
 }IF2ARB2L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _ID24 :1;
    IO_BYTE _ID25 :1;
    IO_BYTE _ID26 :1;
    IO_BYTE _ID27 :1;
    IO_BYTE _ID28 :1;
    IO_BYTE _DIR :1;
    IO_BYTE _XTD :1;
    IO_BYTE _MSGVAL :1;
  }bit;
 }IF2ARB2H1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _DLC0 :1;
    IO_WORD _DLC1 :1;
    IO_WORD _DLC2 :1;
    IO_WORD _DLC3 :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD _EOB :1;
    IO_WORD _TXRQST :1;
    IO_WORD _RMTEN :1;
    IO_WORD _RXIE :1;
    IO_WORD _TXIE :1;
    IO_WORD _UMASK :1;
    IO_WORD _INTPND :1;
    IO_WORD _MSGLST :1;
    IO_WORD _NEWDAT :1;
  }bit;
  struct{
    IO_WORD _DLC :4;
  }bitc;
 }IF2MCTR1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _DLC0 :1;
    IO_BYTE _DLC1 :1;
    IO_BYTE _DLC2 :1;
    IO_BYTE _DLC3 :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE _EOB :1;
  }bit;
  struct{
    IO_BYTE _DLC :4;
  }bitc;
 }IF2MCTRL1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TXRQST :1;
    IO_BYTE _RMTEN :1;
    IO_BYTE _RXIE :1;
    IO_BYTE _TXIE :1;
    IO_BYTE _UMASK :1;
    IO_BYTE _INTPND :1;
    IO_BYTE _MSGLST :1;
    IO_BYTE _NEWDAT :1;
  }bit;
 }IF2MCTRH1STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
  }bit;
 }IF2DTA1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF2DTA11STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF2DTA1L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF2DTA1H1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF2DTA21STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF2DTA2L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF2DTA2H1STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
    IO_LWORD  :1;
  }bit;
 }IF2DTB1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF2DTB11STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF2DTB1L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF2DTB1H1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
    IO_WORD  :1;
  }bit;
 }IF2DTB21STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF2DTB2L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }IF2DTB2H1STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD _TXRQST1 :1;
    IO_LWORD _TXRQST2 :1;
    IO_LWORD _TXRQST3 :1;
    IO_LWORD _TXRQST4 :1;
    IO_LWORD _TXRQST5 :1;
    IO_LWORD _TXRQST6 :1;
    IO_LWORD _TXRQST7 :1;
    IO_LWORD _TXRQST8 :1;
    IO_LWORD _TXRQST9 :1;
    IO_LWORD _TXRQST10 :1;
    IO_LWORD _TXRQST11 :1;
    IO_LWORD _TXRQST12 :1;
    IO_LWORD _TXRQST13 :1;
    IO_LWORD _TXRQST14 :1;
    IO_LWORD _TXRQST15 :1;
    IO_LWORD _TXRQST16 :1;
    IO_LWORD _TXRQST17 :1;
    IO_LWORD _TXRQST18 :1;
    IO_LWORD _TXRQST19 :1;
    IO_LWORD _TXRQST20 :1;
    IO_LWORD _TXRQST21 :1;
    IO_LWORD _TXRQST22 :1;
    IO_LWORD _TXRQST23 :1;
    IO_LWORD _TXRQST24 :1;
    IO_LWORD _TXRQST25 :1;
    IO_LWORD _TXRQST26 :1;
    IO_LWORD _TXRQST27 :1;
    IO_LWORD _TXRQST28 :1;
    IO_LWORD _TXRQST29 :1;
    IO_LWORD _TXRQST30 :1;
    IO_LWORD _TXRQST31 :1;
    IO_LWORD _TXRQST32 :1;
  }bit;
  struct{
    IO_LWORD _TXRQST :32;
  }bitc;
 }TREQR1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TXRQST1 :1;
    IO_WORD _TXRQST2 :1;
    IO_WORD _TXRQST3 :1;
    IO_WORD _TXRQST4 :1;
    IO_WORD _TXRQST5 :1;
    IO_WORD _TXRQST6 :1;
    IO_WORD _TXRQST7 :1;
    IO_WORD _TXRQST8 :1;
    IO_WORD _TXRQST9 :1;
    IO_WORD _TXRQST10 :1;
    IO_WORD _TXRQST11 :1;
    IO_WORD _TXRQST12 :1;
    IO_WORD _TXRQST13 :1;
    IO_WORD _TXRQST14 :1;
    IO_WORD _TXRQST15 :1;
    IO_WORD _TXRQST16 :1;
  }bit;
 }TREQR11STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TXRQST1 :1;
    IO_BYTE _TXRQST2 :1;
    IO_BYTE _TXRQST3 :1;
    IO_BYTE _TXRQST4 :1;
    IO_BYTE _TXRQST5 :1;
    IO_BYTE _TXRQST6 :1;
    IO_BYTE _TXRQST7 :1;
    IO_BYTE _TXRQST8 :1;
  }bit;
 }TREQR1L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TXRQST9 :1;
    IO_BYTE _TXRQST10 :1;
    IO_BYTE _TXRQST11 :1;
    IO_BYTE _TXRQST12 :1;
    IO_BYTE _TXRQST13 :1;
    IO_BYTE _TXRQST14 :1;
    IO_BYTE _TXRQST15 :1;
    IO_BYTE _TXRQST16 :1;
  }bit;
 }TREQR1H1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _TXRQST17 :1;
    IO_WORD _TXRQST18 :1;
    IO_WORD _TXRQST19 :1;
    IO_WORD _TXRQST20 :1;
    IO_WORD _TXRQST21 :1;
    IO_WORD _TXRQST22 :1;
    IO_WORD _TXRQST23 :1;
    IO_WORD _TXRQST24 :1;
    IO_WORD _TXRQST25 :1;
    IO_WORD _TXRQST26 :1;
    IO_WORD _TXRQST27 :1;
    IO_WORD _TXRQST28 :1;
    IO_WORD _TXRQST29 :1;
    IO_WORD _TXRQST30 :1;
    IO_WORD _TXRQST31 :1;
    IO_WORD _TXRQST32 :1;
  }bit;
 }TREQR21STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TXRQST17 :1;
    IO_BYTE _TXRQST18 :1;
    IO_BYTE _TXRQST19 :1;
    IO_BYTE _TXRQST20 :1;
    IO_BYTE _TXRQST21 :1;
    IO_BYTE _TXRQST22 :1;
    IO_BYTE _TXRQST23 :1;
    IO_BYTE _TXRQST24 :1;
  }bit;
 }TREQR2L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _TXRQST25 :1;
    IO_BYTE _TXRQST26 :1;
    IO_BYTE _TXRQST27 :1;
    IO_BYTE _TXRQST28 :1;
    IO_BYTE _TXRQST29 :1;
    IO_BYTE _TXRQST30 :1;
    IO_BYTE _TXRQST31 :1;
    IO_BYTE _TXRQST32 :1;
  }bit;
 }TREQR2H1STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD _NEWDAT1 :1;
    IO_LWORD _NEWDAT2 :1;
    IO_LWORD _NEWDAT3 :1;
    IO_LWORD _NEWDAT4 :1;
    IO_LWORD _NEWDAT5 :1;
    IO_LWORD _NEWDAT6 :1;
    IO_LWORD _NEWDAT7 :1;
    IO_LWORD _NEWDAT8 :1;
    IO_LWORD _NEWDAT9 :1;
    IO_LWORD _NEWDAT10 :1;
    IO_LWORD _NEWDAT11 :1;
    IO_LWORD _NEWDAT12 :1;
    IO_LWORD _NEWDAT13 :1;
    IO_LWORD _NEWDAT14 :1;
    IO_LWORD _NEWDAT15 :1;
    IO_LWORD _NEWDAT16 :1;
    IO_LWORD _NEWDAT17 :1;
    IO_LWORD _NEWDAT18 :1;
    IO_LWORD _NEWDAT19 :1;
    IO_LWORD _NEWDAT20 :1;
    IO_LWORD _NEWDAT21 :1;
    IO_LWORD _NEWDAT22 :1;
    IO_LWORD _NEWDAT23 :1;
    IO_LWORD _NEWDAT24 :1;
    IO_LWORD _NEWDAT25 :1;
    IO_LWORD _NEWDAT26 :1;
    IO_LWORD _NEWDAT27 :1;
    IO_LWORD _NEWDAT28 :1;
    IO_LWORD _NEWDAT29 :1;
    IO_LWORD _NEWDAT30 :1;
    IO_LWORD _NEWDAT31 :1;
    IO_LWORD _NEWDAT32 :1;
  }bit;
  struct{
    IO_LWORD _NEWDAT :32;
  }bitc;
 }NEWDT1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _NEWDAT1 :1;
    IO_WORD _NEWDAT2 :1;
    IO_WORD _NEWDAT3 :1;
    IO_WORD _NEWDAT4 :1;
    IO_WORD _NEWDAT5 :1;
    IO_WORD _NEWDAT6 :1;
    IO_WORD _NEWDAT7 :1;
    IO_WORD _NEWDAT8 :1;
    IO_WORD _NEWDAT9 :1;
    IO_WORD _NEWDAT10 :1;
    IO_WORD _NEWDAT11 :1;
    IO_WORD _NEWDAT12 :1;
    IO_WORD _NEWDAT13 :1;
    IO_WORD _NEWDAT14 :1;
    IO_WORD _NEWDAT15 :1;
    IO_WORD _NEWDAT16 :1;
  }bit;
 }NEWDT11STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _NEWDAT1 :1;
    IO_BYTE _NEWDAT2 :1;
    IO_BYTE _NEWDAT3 :1;
    IO_BYTE _NEWDAT4 :1;
    IO_BYTE _NEWDAT5 :1;
    IO_BYTE _NEWDAT6 :1;
    IO_BYTE _NEWDAT7 :1;
    IO_BYTE _NEWDAT8 :1;
  }bit;
 }NEWDT1L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _NEWDAT9 :1;
    IO_BYTE _NEWDAT10 :1;
    IO_BYTE _NEWDAT11 :1;
    IO_BYTE _NEWDAT12 :1;
    IO_BYTE _NEWDAT13 :1;
    IO_BYTE _NEWDAT14 :1;
    IO_BYTE _NEWDAT15 :1;
    IO_BYTE _NEWDAT16 :1;
  }bit;
 }NEWDT1H1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _NEWDAT17 :1;
    IO_WORD _NEWDAT18 :1;
    IO_WORD _NEWDAT19 :1;
    IO_WORD _NEWDAT20 :1;
    IO_WORD _NEWDAT21 :1;
    IO_WORD _NEWDAT22 :1;
    IO_WORD _NEWDAT23 :1;
    IO_WORD _NEWDAT24 :1;
    IO_WORD _NEWDAT25 :1;
    IO_WORD _NEWDAT26 :1;
    IO_WORD _NEWDAT27 :1;
    IO_WORD _NEWDAT28 :1;
    IO_WORD _NEWDAT29 :1;
    IO_WORD _NEWDAT30 :1;
    IO_WORD _NEWDAT31 :1;
    IO_WORD _NEWDAT32 :1;
  }bit;
 }NEWDT21STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _NEWDAT17 :1;
    IO_BYTE _NEWDAT18 :1;
    IO_BYTE _NEWDAT19 :1;
    IO_BYTE _NEWDAT20 :1;
    IO_BYTE _NEWDAT21 :1;
    IO_BYTE _NEWDAT22 :1;
    IO_BYTE _NEWDAT23 :1;
    IO_BYTE _NEWDAT24 :1;
  }bit;
 }NEWDT2L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _NEWDAT25 :1;
    IO_BYTE _NEWDAT26 :1;
    IO_BYTE _NEWDAT27 :1;
    IO_BYTE _NEWDAT28 :1;
    IO_BYTE _NEWDAT29 :1;
    IO_BYTE _NEWDAT30 :1;
    IO_BYTE _NEWDAT31 :1;
    IO_BYTE _NEWDAT32 :1;
  }bit;
 }NEWDT2H1STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD _INTPND1 :1;
    IO_LWORD _INTPND2 :1;
    IO_LWORD _INTPND3 :1;
    IO_LWORD _INTPND4 :1;
    IO_LWORD _INTPND5 :1;
    IO_LWORD _INTPND6 :1;
    IO_LWORD _INTPND7 :1;
    IO_LWORD _INTPND8 :1;
    IO_LWORD _INTPND9 :1;
    IO_LWORD _INTPND10 :1;
    IO_LWORD _INTPND11 :1;
    IO_LWORD _INTPND12 :1;
    IO_LWORD _INTPND13 :1;
    IO_LWORD _INTPND14 :1;
    IO_LWORD _INTPND15 :1;
    IO_LWORD _INTPND16 :1;
    IO_LWORD _INTPND17 :1;
    IO_LWORD _INTPND18 :1;
    IO_LWORD _INTPND19 :1;
    IO_LWORD _INTPND20 :1;
    IO_LWORD _INTPND21 :1;
    IO_LWORD _INTPND22 :1;
    IO_LWORD _INTPND23 :1;
    IO_LWORD _INTPND24 :1;
    IO_LWORD _INTPND25 :1;
    IO_LWORD _INTPND26 :1;
    IO_LWORD _INTPND27 :1;
    IO_LWORD _INTPND28 :1;
    IO_LWORD _INTPND29 :1;
    IO_LWORD _INTPND30 :1;
    IO_LWORD _INTPND31 :1;
    IO_LWORD _INTPND32 :1;
  }bit;
  struct{
    IO_LWORD _INTPND :32;
  }bitc;
 }INTPND1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _INTPND1 :1;
    IO_WORD _INTPND2 :1;
    IO_WORD _INTPND3 :1;
    IO_WORD _INTPND4 :1;
    IO_WORD _INTPND5 :1;
    IO_WORD _INTPND6 :1;
    IO_WORD _INTPND7 :1;
    IO_WORD _INTPND8 :1;
    IO_WORD _INTPND9 :1;
    IO_WORD _INTPND10 :1;
    IO_WORD _INTPND11 :1;
    IO_WORD _INTPND12 :1;
    IO_WORD _INTPND13 :1;
    IO_WORD _INTPND14 :1;
    IO_WORD _INTPND15 :1;
    IO_WORD _INTPND16 :1;
  }bit;
 }INTPND11STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INTPND1 :1;
    IO_BYTE _INTPND2 :1;
    IO_BYTE _INTPND3 :1;
    IO_BYTE _INTPND4 :1;
    IO_BYTE _INTPND5 :1;
    IO_BYTE _INTPND6 :1;
    IO_BYTE _INTPND7 :1;
    IO_BYTE _INTPND8 :1;
  }bit;
 }INTPND1L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INTPND9 :1;
    IO_BYTE _INTPND10 :1;
    IO_BYTE _INTPND11 :1;
    IO_BYTE _INTPND12 :1;
    IO_BYTE _INTPND13 :1;
    IO_BYTE _INTPND14 :1;
    IO_BYTE _INTPND15 :1;
    IO_BYTE _INTPND16 :1;
  }bit;
 }INTPND1H1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _INTPND17 :1;
    IO_WORD _INTPND18 :1;
    IO_WORD _INTPND19 :1;
    IO_WORD _INTPND20 :1;
    IO_WORD _INTPND21 :1;
    IO_WORD _INTPND22 :1;
    IO_WORD _INTPND23 :1;
    IO_WORD _INTPND24 :1;
    IO_WORD _INTPND25 :1;
    IO_WORD _INTPND26 :1;
    IO_WORD _INTPND27 :1;
    IO_WORD _INTPND28 :1;
    IO_WORD _INTPND29 :1;
    IO_WORD _INTPND30 :1;
    IO_WORD _INTPND31 :1;
    IO_WORD _INTPND32 :1;
  }bit;
 }INTPND21STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INTPND17 :1;
    IO_BYTE _INTPND18 :1;
    IO_BYTE _INTPND19 :1;
    IO_BYTE _INTPND20 :1;
    IO_BYTE _INTPND21 :1;
    IO_BYTE _INTPND22 :1;
    IO_BYTE _INTPND23 :1;
    IO_BYTE _INTPND24 :1;
  }bit;
 }INTPND2L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _INTPND25 :1;
    IO_BYTE _INTPND26 :1;
    IO_BYTE _INTPND27 :1;
    IO_BYTE _INTPND28 :1;
    IO_BYTE _INTPND29 :1;
    IO_BYTE _INTPND30 :1;
    IO_BYTE _INTPND31 :1;
    IO_BYTE _INTPND32 :1;
  }bit;
 }INTPND2H1STR;
typedef union{  
    IO_LWORD	lword;
    struct{
    IO_LWORD _MSGVAL1 :1;
    IO_LWORD _MSGVAL2 :1;
    IO_LWORD _MSGVAL3 :1;
    IO_LWORD _MSGVAL4 :1;
    IO_LWORD _MSGVAL5 :1;
    IO_LWORD _MSGVAL6 :1;
    IO_LWORD _MSGVAL7 :1;
    IO_LWORD _MSGVAL8 :1;
    IO_LWORD _MSGVAL9 :1;
    IO_LWORD _MSGVAL10 :1;
    IO_LWORD _MSGVAL11 :1;
    IO_LWORD _MSGVAL12 :1;
    IO_LWORD _MSGVAL13 :1;
    IO_LWORD _MSGVAL14 :1;
    IO_LWORD _MSGVAL15 :1;
    IO_LWORD _MSGVAL16 :1;
    IO_LWORD _MSGVAL17 :1;
    IO_LWORD _MSGVAL18 :1;
    IO_LWORD _MSGVAL19 :1;
    IO_LWORD _MSGVAL20 :1;
    IO_LWORD _MSGVAL21 :1;
    IO_LWORD _MSGVAL22 :1;
    IO_LWORD _MSGVAL23 :1;
    IO_LWORD _MSGVAL24 :1;
    IO_LWORD _MSGVAL25 :1;
    IO_LWORD _MSGVAL26 :1;
    IO_LWORD _MSGVAL27 :1;
    IO_LWORD _MSGVAL28 :1;
    IO_LWORD _MSGVAL29 :1;
    IO_LWORD _MSGVAL30 :1;
    IO_LWORD _MSGVAL31 :1;
    IO_LWORD _MSGVAL32 :1;
  }bit;
  struct{
    IO_LWORD _MSGVAL :32;
  }bitc;
 }MSGVAL1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _MSGVAL1 :1;
    IO_WORD _MSGVAL2 :1;
    IO_WORD _MSGVAL3 :1;
    IO_WORD _MSGVAL4 :1;
    IO_WORD _MSGVAL5 :1;
    IO_WORD _MSGVAL6 :1;
    IO_WORD _MSGVAL7 :1;
    IO_WORD _MSGVAL8 :1;
    IO_WORD _MSGVAL9 :1;
    IO_WORD _MSGVAL10 :1;
    IO_WORD _MSGVAL11 :1;
    IO_WORD _MSGVAL12 :1;
    IO_WORD _MSGVAL13 :1;
    IO_WORD _MSGVAL14 :1;
    IO_WORD _MSGVAL15 :1;
    IO_WORD _MSGVAL16 :1;
  }bit;
 }MSGVAL11STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSGVAL1 :1;
    IO_BYTE _MSGVAL2 :1;
    IO_BYTE _MSGVAL3 :1;
    IO_BYTE _MSGVAL4 :1;
    IO_BYTE _MSGVAL5 :1;
    IO_BYTE _MSGVAL6 :1;
    IO_BYTE _MSGVAL7 :1;
    IO_BYTE _MSGVAL8 :1;
  }bit;
 }MSGVAL1L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSGVAL9 :1;
    IO_BYTE _MSGVAL10 :1;
    IO_BYTE _MSGVAL11 :1;
    IO_BYTE _MSGVAL12 :1;
    IO_BYTE _MSGVAL13 :1;
    IO_BYTE _MSGVAL14 :1;
    IO_BYTE _MSGVAL15 :1;
    IO_BYTE _MSGVAL16 :1;
  }bit;
 }MSGVAL1H1STR;
typedef union{  
    IO_WORD	word;
    struct{
    IO_WORD _MSGVAL17 :1;
    IO_WORD _MSGVAL18 :1;
    IO_WORD _MSGVAL19 :1;
    IO_WORD _MSGVAL20 :1;
    IO_WORD _MSGVAL21 :1;
    IO_WORD _MSGVAL22 :1;
    IO_WORD _MSGVAL23 :1;
    IO_WORD _MSGVAL24 :1;
    IO_WORD _MSGVAL25 :1;
    IO_WORD _MSGVAL26 :1;
    IO_WORD _MSGVAL27 :1;
    IO_WORD _MSGVAL28 :1;
    IO_WORD _MSGVAL29 :1;
    IO_WORD _MSGVAL30 :1;
    IO_WORD _MSGVAL31 :1;
    IO_WORD _MSGVAL32 :1;
  }bit;
 }MSGVAL21STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSGVAL17 :1;
    IO_BYTE _MSGVAL18 :1;
    IO_BYTE _MSGVAL19 :1;
    IO_BYTE _MSGVAL20 :1;
    IO_BYTE _MSGVAL21 :1;
    IO_BYTE _MSGVAL22 :1;
    IO_BYTE _MSGVAL23 :1;
    IO_BYTE _MSGVAL24 :1;
  }bit;
 }MSGVAL2L1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _MSGVAL25 :1;
    IO_BYTE _MSGVAL26 :1;
    IO_BYTE _MSGVAL27 :1;
    IO_BYTE _MSGVAL28 :1;
    IO_BYTE _MSGVAL29 :1;
    IO_BYTE _MSGVAL30 :1;
    IO_BYTE _MSGVAL31 :1;
    IO_BYTE _MSGVAL32 :1;
  }bit;
 }MSGVAL2H1STR;
typedef union{  
    IO_BYTE	byte;
    struct{
    IO_BYTE _OE :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
    IO_BYTE  :1;
  }bit;
 }COER1STR;

/* C-DECLARATIONS */

__IO_EXTERN __io PDR00STR _pdr00;  
#define PDR00 _pdr00.byte
#define PDR00_P0 _pdr00.bit._P0
#define PDR00_P1 _pdr00.bit._P1
#define PDR00_P2 _pdr00.bit._P2
#define PDR00_P3 _pdr00.bit._P3
#define PDR00_P4 _pdr00.bit._P4
#define PDR00_P5 _pdr00.bit._P5
#define PDR00_P6 _pdr00.bit._P6
#define PDR00_P7 _pdr00.bit._P7
__IO_EXTERN __io PDR01STR _pdr01;  
#define PDR01 _pdr01.byte
#define PDR01_P0 _pdr01.bit._P0
#define PDR01_P1 _pdr01.bit._P1
#define PDR01_P2 _pdr01.bit._P2
#define PDR01_P3 _pdr01.bit._P3
#define PDR01_P4 _pdr01.bit._P4
#define PDR01_P5 _pdr01.bit._P5
#define PDR01_P6 _pdr01.bit._P6
#define PDR01_P7 _pdr01.bit._P7
__IO_EXTERN __io PDR02STR _pdr02;  
#define PDR02 _pdr02.byte
#define PDR02_P0 _pdr02.bit._P0
#define PDR02_P1 _pdr02.bit._P1
#define PDR02_P2 _pdr02.bit._P2
#define PDR02_P3 _pdr02.bit._P3
#define PDR02_P4 _pdr02.bit._P4
#define PDR02_P5 _pdr02.bit._P5
#define PDR02_P6 _pdr02.bit._P6
#define PDR02_P7 _pdr02.bit._P7
__IO_EXTERN __io PDR03STR _pdr03;  
#define PDR03 _pdr03.byte
#define PDR03_P0 _pdr03.bit._P0
#define PDR03_P1 _pdr03.bit._P1
#define PDR03_P2 _pdr03.bit._P2
#define PDR03_P3 _pdr03.bit._P3
#define PDR03_P4 _pdr03.bit._P4
#define PDR03_P5 _pdr03.bit._P5
#define PDR03_P6 _pdr03.bit._P6
#define PDR03_P7 _pdr03.bit._P7
__IO_EXTERN __io PDR04STR _pdr04;  
#define PDR04 _pdr04.byte
#define PDR04_P0 _pdr04.bit._P0
#define PDR04_P1 _pdr04.bit._P1
#define PDR04_P2 _pdr04.bit._P2
#define PDR04_P3 _pdr04.bit._P3
#define PDR04_P4 _pdr04.bit._P4
#define PDR04_P5 _pdr04.bit._P5
#define PDR04_P6 _pdr04.bit._P6
#define PDR04_P7 _pdr04.bit._P7
__IO_EXTERN __io PDR05STR _pdr05;  
#define PDR05 _pdr05.byte
#define PDR05_P0 _pdr05.bit._P0
#define PDR05_P1 _pdr05.bit._P1
#define PDR05_P2 _pdr05.bit._P2
#define PDR05_P3 _pdr05.bit._P3
#define PDR05_P4 _pdr05.bit._P4
#define PDR05_P5 _pdr05.bit._P5
#define PDR05_P6 _pdr05.bit._P6
#define PDR05_P7 _pdr05.bit._P7
__IO_EXTERN __io PDR06STR _pdr06;  
#define PDR06 _pdr06.byte
#define PDR06_P0 _pdr06.bit._P0
#define PDR06_P1 _pdr06.bit._P1
#define PDR06_P2 _pdr06.bit._P2
#define PDR06_P3 _pdr06.bit._P3
#define PDR06_P4 _pdr06.bit._P4
#define PDR06_P5 _pdr06.bit._P5
#define PDR06_P6 _pdr06.bit._P6
#define PDR06_P7 _pdr06.bit._P7
__IO_EXTERN __io PDR07STR _pdr07;  
#define PDR07 _pdr07.byte
#define PDR07_P0 _pdr07.bit._P0
#define PDR07_P1 _pdr07.bit._P1
#define PDR07_P2 _pdr07.bit._P2
#define PDR07_P3 _pdr07.bit._P3
#define PDR07_P4 _pdr07.bit._P4
#define PDR07_P5 _pdr07.bit._P5
#define PDR07_P6 _pdr07.bit._P6
#define PDR07_P7 _pdr07.bit._P7
__IO_EXTERN __io PDR08STR _pdr08;  
#define PDR08 _pdr08.byte
#define PDR08_P0 _pdr08.bit._P0
#define PDR08_P1 _pdr08.bit._P1
#define PDR08_P2 _pdr08.bit._P2
#define PDR08_P3 _pdr08.bit._P3
#define PDR08_P4 _pdr08.bit._P4
#define PDR08_P5 _pdr08.bit._P5
#define PDR08_P6 _pdr08.bit._P6
#define PDR08_P7 _pdr08.bit._P7
__IO_EXTERN __io PDR09STR _pdr09;  
#define PDR09 _pdr09.byte
#define PDR09_P0 _pdr09.bit._P0
#define PDR09_P1 _pdr09.bit._P1
#define PDR09_P2 _pdr09.bit._P2
#define PDR09_P3 _pdr09.bit._P3
#define PDR09_P4 _pdr09.bit._P4
#define PDR09_P5 _pdr09.bit._P5
#define PDR09_P6 _pdr09.bit._P6
#define PDR09_P7 _pdr09.bit._P7
__IO_EXTERN __io PDR10STR _pdr10;  
#define PDR10 _pdr10.byte
#define PDR10_P0 _pdr10.bit._P0
#define PDR10_P1 _pdr10.bit._P1
__IO_EXTERN __io ADCSSTR _adcs;  
#define ADCS _adcs.word
#define ADCS_resv _adcs.bit._resv
#define ADCS_S10 _adcs.bit._S10
#define ADCS_MD0 _adcs.bit._MD0
#define ADCS_MD1 _adcs.bit._MD1
#define ADCS_STRT _adcs.bit._STRT
#define ADCS_STS0 _adcs.bit._STS0
#define ADCS_STS1 _adcs.bit._STS1
#define ADCS_PAUS _adcs.bit._PAUS
#define ADCS_INTE _adcs.bit._INTE
#define ADCS_INT _adcs.bit._INT
#define ADCS_BUSY _adcs.bit._BUSY
#define ADCS_MD _adcs.bitc._MD
#define ADCS_STS _adcs.bitc._STS
__IO_EXTERN __io ADCSLSTR _adcsl;  
#define ADCSL _adcsl.byte
#define ADCSL_resv _adcsl.bit._resv
#define ADCSL_S10 _adcsl.bit._S10
#define ADCSL_MD0 _adcsl.bit._MD0
#define ADCSL_MD1 _adcsl.bit._MD1
#define ADCSL_MD _adcsl.bitc._MD
__IO_EXTERN __io ADCSHSTR _adcsh;  
#define ADCSH _adcsh.byte
#define ADCSH_STRT _adcsh.bit._STRT
#define ADCSH_STS0 _adcsh.bit._STS0
#define ADCSH_STS1 _adcsh.bit._STS1
#define ADCSH_PAUS _adcsh.bit._PAUS
#define ADCSH_INTE _adcsh.bit._INTE
#define ADCSH_INT _adcsh.bit._INT
#define ADCSH_BUSY _adcsh.bit._BUSY
#define ADCSH_STS _adcsh.bitc._STS
__IO_EXTERN __io ADCRSTR _adcr;  
#define ADCR _adcr.word
#define ADCR_D0 _adcr.bit._D0
#define ADCR_D1 _adcr.bit._D1
#define ADCR_D2 _adcr.bit._D2
#define ADCR_D3 _adcr.bit._D3
#define ADCR_D4 _adcr.bit._D4
#define ADCR_D5 _adcr.bit._D5
#define ADCR_D6 _adcr.bit._D6
#define ADCR_D7 _adcr.bit._D7
#define ADCR_D8 _adcr.bit._D8
#define ADCR_D9 _adcr.bit._D9
#define ADCR_D _adcr.bitc._D
__IO_EXTERN __io ADCRLSTR _adcrl;  
#define ADCRL _adcrl.byte
#define ADCRL_D0 _adcrl.bit._D0
#define ADCRL_D1 _adcrl.bit._D1
#define ADCRL_D2 _adcrl.bit._D2
#define ADCRL_D3 _adcrl.bit._D3
#define ADCRL_D4 _adcrl.bit._D4
#define ADCRL_D5 _adcrl.bit._D5
#define ADCRL_D6 _adcrl.bit._D6
#define ADCRL_D7 _adcrl.bit._D7
__IO_EXTERN __io ADCRHSTR _adcrh;  
#define ADCRH _adcrh.byte
#define ADCRH_D8 _adcrh.bit._D8
#define ADCRH_D9 _adcrh.bit._D9
__IO_EXTERN __io ADSRSTR _adsr;  
#define ADSR _adsr.word
#define ADSR_ANE0 _adsr.bit._ANE0
#define ADSR_ANE1 _adsr.bit._ANE1
#define ADSR_ANE2 _adsr.bit._ANE2
#define ADSR_ANE3 _adsr.bit._ANE3
#define ADSR_ANE4 _adsr.bit._ANE4
#define ADSR_ANS0 _adsr.bit._ANS0
#define ADSR_ANS1 _adsr.bit._ANS1
#define ADSR_ANS2 _adsr.bit._ANS2
#define ADSR_ANS3 _adsr.bit._ANS3
#define ADSR_ANS4 _adsr.bit._ANS4
#define ADSR_CT0 _adsr.bit._CT0
#define ADSR_CT1 _adsr.bit._CT1
#define ADSR_CT2 _adsr.bit._CT2
#define ADSR_ST0 _adsr.bit._ST0
#define ADSR_ST1 _adsr.bit._ST1
#define ADSR_ST2 _adsr.bit._ST2
__IO_EXTERN __io ADECRSTR _adecr;  
#define ADECR _adecr.byte
#define ADECR_ADSEL _adecr.bit._ADSEL
#define ADECR_HSEL _adecr.bit._HSEL
#define ADECR_LSEL _adecr.bit._LSEL
__IO_EXTERN __io TCDT0STR _tcdt0;  
#define TCDT0 _tcdt0.word
#define TCDT0_T0 _tcdt0.bit._T0
#define TCDT0_T1 _tcdt0.bit._T1
#define TCDT0_T2 _tcdt0.bit._T2
#define TCDT0_T3 _tcdt0.bit._T3
#define TCDT0_T4 _tcdt0.bit._T4
#define TCDT0_T5 _tcdt0.bit._T5
#define TCDT0_T6 _tcdt0.bit._T6
#define TCDT0_T7 _tcdt0.bit._T7
#define TCDT0_T8 _tcdt0.bit._T8
#define TCDT0_T9 _tcdt0.bit._T9
#define TCDT0_T10 _tcdt0.bit._T10
#define TCDT0_T11 _tcdt0.bit._T11
#define TCDT0_T12 _tcdt0.bit._T12
#define TCDT0_T13 _tcdt0.bit._T13
#define TCDT0_T14 _tcdt0.bit._T14
#define TCDT0_T15 _tcdt0.bit._T15
#define TCDT0_T _tcdt0.bitc._T
__IO_EXTERN __io TCCS0STR _tccs0;  
#define TCCS0 _tccs0.word
#define TCCS0_CLK0 _tccs0.bit._CLK0
#define TCCS0_CLK1 _tccs0.bit._CLK1
#define TCCS0_CLK2 _tccs0.bit._CLK2
#define TCCS0_CLR _tccs0.bit._CLR
#define TCCS0_MODE _tccs0.bit._MODE
#define TCCS0_STOP _tccs0.bit._STOP
#define TCCS0_IVFE _tccs0.bit._IVFE
#define TCCS0_IVF _tccs0.bit._IVF
#define TCCS0_FSEL _tccs0.bit._FSEL
#define TCCS0_ECKE _tccs0.bit._ECKE
#define TCCS0_CLK _tccs0.bitc._CLK
__IO_EXTERN __io TCCSL0STR _tccsl0;  
#define TCCSL0 _tccsl0.byte
#define TCCSL0_CLK0 _tccsl0.bit._CLK0
#define TCCSL0_CLK1 _tccsl0.bit._CLK1
#define TCCSL0_CLK2 _tccsl0.bit._CLK2
#define TCCSL0_CLR _tccsl0.bit._CLR
#define TCCSL0_MODE _tccsl0.bit._MODE
#define TCCSL0_STOP _tccsl0.bit._STOP
#define TCCSL0_IVFE _tccsl0.bit._IVFE
#define TCCSL0_IVF _tccsl0.bit._IVF
#define TCCSL0_CLK _tccsl0.bitc._CLK
__IO_EXTERN __io TCCSH0STR _tccsh0;  
#define TCCSH0 _tccsh0.byte
#define TCCSH0_FSEL _tccsh0.bit._FSEL
#define TCCSH0_ECKE _tccsh0.bit._ECKE
__IO_EXTERN __io TCDT1STR _tcdt1;  
#define TCDT1 _tcdt1.word
#define TCDT1_T0 _tcdt1.bit._T0
#define TCDT1_T1 _tcdt1.bit._T1
#define TCDT1_T2 _tcdt1.bit._T2
#define TCDT1_T3 _tcdt1.bit._T3
#define TCDT1_T4 _tcdt1.bit._T4
#define TCDT1_T5 _tcdt1.bit._T5
#define TCDT1_T6 _tcdt1.bit._T6
#define TCDT1_T7 _tcdt1.bit._T7
#define TCDT1_T8 _tcdt1.bit._T8
#define TCDT1_T9 _tcdt1.bit._T9
#define TCDT1_T10 _tcdt1.bit._T10
#define TCDT1_T11 _tcdt1.bit._T11
#define TCDT1_T12 _tcdt1.bit._T12
#define TCDT1_T13 _tcdt1.bit._T13
#define TCDT1_T14 _tcdt1.bit._T14
#define TCDT1_T15 _tcdt1.bit._T15
#define TCDT1_T _tcdt1.bitc._T
__IO_EXTERN __io TCCS1STR _tccs1;  
#define TCCS1 _tccs1.word
#define TCCS1_CLK0 _tccs1.bit._CLK0
#define TCCS1_CLK1 _tccs1.bit._CLK1
#define TCCS1_CLK2 _tccs1.bit._CLK2
#define TCCS1_CLR _tccs1.bit._CLR
#define TCCS1_MODE _tccs1.bit._MODE
#define TCCS1_STOP _tccs1.bit._STOP
#define TCCS1_IVFE _tccs1.bit._IVFE
#define TCCS1_IVF _tccs1.bit._IVF
#define TCCS1_FSEL _tccs1.bit._FSEL
#define TCCS1_ECKE _tccs1.bit._ECKE
#define TCCS1_CLK _tccs1.bitc._CLK
__IO_EXTERN __io TCCSL1STR _tccsl1;  
#define TCCSL1 _tccsl1.byte
#define TCCSL1_CLK0 _tccsl1.bit._CLK0
#define TCCSL1_CLK1 _tccsl1.bit._CLK1
#define TCCSL1_CLK2 _tccsl1.bit._CLK2
#define TCCSL1_CLR _tccsl1.bit._CLR
#define TCCSL1_MODE _tccsl1.bit._MODE
#define TCCSL1_STOP _tccsl1.bit._STOP
#define TCCSL1_IVFE _tccsl1.bit._IVFE
#define TCCSL1_IVF _tccsl1.bit._IVF
#define TCCSL1_CLK _tccsl1.bitc._CLK
__IO_EXTERN __io TCCSH1STR _tccsh1;  
#define TCCSH1 _tccsh1.byte
#define TCCSH1_FSEL _tccsh1.bit._FSEL
#define TCCSH1_ECKE _tccsh1.bit._ECKE
__IO_EXTERN __io OCS0STR _ocs0;  
#define OCS0 _ocs0.byte
#define OCS0_CST0 _ocs0.bit._CST0
#define OCS0_CST1 _ocs0.bit._CST1
#define OCS0_ICE0 _ocs0.bit._ICE0
#define OCS0_ICE1 _ocs0.bit._ICE1
#define OCS0_ICP0 _ocs0.bit._ICP0
#define OCS0_ICP1 _ocs0.bit._ICP1
__IO_EXTERN __io OCS1STR _ocs1;  
#define OCS1 _ocs1.byte
#define OCS1_OTD0 _ocs1.bit._OTD0
#define OCS1_OTD1 _ocs1.bit._OTD1
#define OCS1_OTE0 _ocs1.bit._OTE0
#define OCS1_OTE1 _ocs1.bit._OTE1
#define OCS1_CMOD0 _ocs1.bit._CMOD0
#define OCS1_CMOD1 _ocs1.bit._CMOD1
__IO_EXTERN __io OCCP0STR _occp0;  
#define OCCP0 _occp0.word
#define OCCP0_C00 _occp0.bit._C00
#define OCCP0_C01 _occp0.bit._C01
#define OCCP0_C02 _occp0.bit._C02
#define OCCP0_C03 _occp0.bit._C03
#define OCCP0_C04 _occp0.bit._C04
#define OCCP0_C05 _occp0.bit._C05
#define OCCP0_C06 _occp0.bit._C06
#define OCCP0_C07 _occp0.bit._C07
#define OCCP0_C08 _occp0.bit._C08
#define OCCP0_C09 _occp0.bit._C09
#define OCCP0_C10 _occp0.bit._C10
#define OCCP0_C11 _occp0.bit._C11
#define OCCP0_C12 _occp0.bit._C12
#define OCCP0_C13 _occp0.bit._C13
#define OCCP0_C14 _occp0.bit._C14
#define OCCP0_C15 _occp0.bit._C15
#define OCCP0_C0 _occp0.bitc._C0
__IO_EXTERN __io OCCP1STR _occp1;  
#define OCCP1 _occp1.word
#define OCCP1_C00 _occp1.bit._C00
#define OCCP1_C01 _occp1.bit._C01
#define OCCP1_C02 _occp1.bit._C02
#define OCCP1_C03 _occp1.bit._C03
#define OCCP1_C04 _occp1.bit._C04
#define OCCP1_C05 _occp1.bit._C05
#define OCCP1_C06 _occp1.bit._C06
#define OCCP1_C07 _occp1.bit._C07
#define OCCP1_C08 _occp1.bit._C08
#define OCCP1_C09 _occp1.bit._C09
#define OCCP1_C10 _occp1.bit._C10
#define OCCP1_C11 _occp1.bit._C11
#define OCCP1_C12 _occp1.bit._C12
#define OCCP1_C13 _occp1.bit._C13
#define OCCP1_C14 _occp1.bit._C14
#define OCCP1_C15 _occp1.bit._C15
#define OCCP1_C0 _occp1.bitc._C0
__IO_EXTERN __io OCS2STR _ocs2;  
#define OCS2 _ocs2.byte
#define OCS2_CST2 _ocs2.bit._CST2
#define OCS2_CST3 _ocs2.bit._CST3
#define OCS2_ICE2 _ocs2.bit._ICE2
#define OCS2_ICE3 _ocs2.bit._ICE3
#define OCS2_ICP2 _ocs2.bit._ICP2
#define OCS2_ICP3 _ocs2.bit._ICP3
__IO_EXTERN __io OCS3STR _ocs3;  
#define OCS3 _ocs3.byte
#define OCS3_OTD2 _ocs3.bit._OTD2
#define OCS3_OTD3 _ocs3.bit._OTD3
#define OCS3_OTE2 _ocs3.bit._OTE2
#define OCS3_OTE3 _ocs3.bit._OTE3
#define OCS3_CMOD0 _ocs3.bit._CMOD0
#define OCS3_CMOD1 _ocs3.bit._CMOD1
__IO_EXTERN __io OCCP2STR _occp2;  
#define OCCP2 _occp2.word
#define OCCP2_C00 _occp2.bit._C00
#define OCCP2_C01 _occp2.bit._C01
#define OCCP2_C02 _occp2.bit._C02
#define OCCP2_C03 _occp2.bit._C03
#define OCCP2_C04 _occp2.bit._C04
#define OCCP2_C05 _occp2.bit._C05
#define OCCP2_C06 _occp2.bit._C06
#define OCCP2_C07 _occp2.bit._C07
#define OCCP2_C08 _occp2.bit._C08
#define OCCP2_C09 _occp2.bit._C09
#define OCCP2_C10 _occp2.bit._C10
#define OCCP2_C11 _occp2.bit._C11
#define OCCP2_C12 _occp2.bit._C12
#define OCCP2_C13 _occp2.bit._C13
#define OCCP2_C14 _occp2.bit._C14
#define OCCP2_C15 _occp2.bit._C15
#define OCCP2_C0 _occp2.bitc._C0
__IO_EXTERN __io OCCP3STR _occp3;  
#define OCCP3 _occp3.word
#define OCCP3_C00 _occp3.bit._C00
#define OCCP3_C01 _occp3.bit._C01
#define OCCP3_C02 _occp3.bit._C02
#define OCCP3_C03 _occp3.bit._C03
#define OCCP3_C04 _occp3.bit._C04
#define OCCP3_C05 _occp3.bit._C05
#define OCCP3_C06 _occp3.bit._C06
#define OCCP3_C07 _occp3.bit._C07
#define OCCP3_C08 _occp3.bit._C08
#define OCCP3_C09 _occp3.bit._C09
#define OCCP3_C10 _occp3.bit._C10
#define OCCP3_C11 _occp3.bit._C11
#define OCCP3_C12 _occp3.bit._C12
#define OCCP3_C13 _occp3.bit._C13
#define OCCP3_C14 _occp3.bit._C14
#define OCCP3_C15 _occp3.bit._C15
#define OCCP3_C0 _occp3.bitc._C0
__IO_EXTERN __io OCS4STR _ocs4;  
#define OCS4 _ocs4.byte
#define OCS4_CST4 _ocs4.bit._CST4
#define OCS4_CST5 _ocs4.bit._CST5
#define OCS4_ICE4 _ocs4.bit._ICE4
#define OCS4_ICE5 _ocs4.bit._ICE5
#define OCS4_ICP4 _ocs4.bit._ICP4
#define OCS4_ICP5 _ocs4.bit._ICP5
__IO_EXTERN __io OCS5STR _ocs5;  
#define OCS5 _ocs5.byte
#define OCS5_OTD4 _ocs5.bit._OTD4
#define OCS5_OTD5 _ocs5.bit._OTD5
#define OCS5_OTE4 _ocs5.bit._OTE4
#define OCS5_OTE5 _ocs5.bit._OTE5
#define OCS5_CMOD0 _ocs5.bit._CMOD0
#define OCS5_CMOD1 _ocs5.bit._CMOD1
__IO_EXTERN __io OCCP4STR _occp4;  
#define OCCP4 _occp4.word
#define OCCP4_C00 _occp4.bit._C00
#define OCCP4_C01 _occp4.bit._C01
#define OCCP4_C02 _occp4.bit._C02
#define OCCP4_C03 _occp4.bit._C03
#define OCCP4_C04 _occp4.bit._C04
#define OCCP4_C05 _occp4.bit._C05
#define OCCP4_C06 _occp4.bit._C06
#define OCCP4_C07 _occp4.bit._C07
#define OCCP4_C08 _occp4.bit._C08
#define OCCP4_C09 _occp4.bit._C09
#define OCCP4_C10 _occp4.bit._C10
#define OCCP4_C11 _occp4.bit._C11
#define OCCP4_C12 _occp4.bit._C12
#define OCCP4_C13 _occp4.bit._C13
#define OCCP4_C14 _occp4.bit._C14
#define OCCP4_C15 _occp4.bit._C15
#define OCCP4_C0 _occp4.bitc._C0
__IO_EXTERN __io OCCP5STR _occp5;  
#define OCCP5 _occp5.word
#define OCCP5_C00 _occp5.bit._C00
#define OCCP5_C01 _occp5.bit._C01
#define OCCP5_C02 _occp5.bit._C02
#define OCCP5_C03 _occp5.bit._C03
#define OCCP5_C04 _occp5.bit._C04
#define OCCP5_C05 _occp5.bit._C05
#define OCCP5_C06 _occp5.bit._C06
#define OCCP5_C07 _occp5.bit._C07
#define OCCP5_C08 _occp5.bit._C08
#define OCCP5_C09 _occp5.bit._C09
#define OCCP5_C10 _occp5.bit._C10
#define OCCP5_C11 _occp5.bit._C11
#define OCCP5_C12 _occp5.bit._C12
#define OCCP5_C13 _occp5.bit._C13
#define OCCP5_C14 _occp5.bit._C14
#define OCCP5_C15 _occp5.bit._C15
#define OCCP5_C0 _occp5.bitc._C0
__IO_EXTERN __io OCS6STR _ocs6;  
#define OCS6 _ocs6.byte
#define OCS6_CST6 _ocs6.bit._CST6
#define OCS6_CST7 _ocs6.bit._CST7
#define OCS6_ICE6 _ocs6.bit._ICE6
#define OCS6_ICE7 _ocs6.bit._ICE7
#define OCS6_ICP6 _ocs6.bit._ICP6
#define OCS6_ICP7 _ocs6.bit._ICP7
__IO_EXTERN __io OCS7STR _ocs7;  
#define OCS7 _ocs7.byte
#define OCS7_OTD6 _ocs7.bit._OTD6
#define OCS7_OTD7 _ocs7.bit._OTD7
#define OCS7_OTE6 _ocs7.bit._OTE6
#define OCS7_OTE7 _ocs7.bit._OTE7
#define OCS7_CMOD0 _ocs7.bit._CMOD0
#define OCS7_CMOD1 _ocs7.bit._CMOD1
__IO_EXTERN __io OCCP6STR _occp6;  
#define OCCP6 _occp6.word
#define OCCP6_C00 _occp6.bit._C00
#define OCCP6_C01 _occp6.bit._C01
#define OCCP6_C02 _occp6.bit._C02
#define OCCP6_C03 _occp6.bit._C03
#define OCCP6_C04 _occp6.bit._C04
#define OCCP6_C05 _occp6.bit._C05
#define OCCP6_C06 _occp6.bit._C06
#define OCCP6_C07 _occp6.bit._C07
#define OCCP6_C08 _occp6.bit._C08
#define OCCP6_C09 _occp6.bit._C09
#define OCCP6_C10 _occp6.bit._C10
#define OCCP6_C11 _occp6.bit._C11
#define OCCP6_C12 _occp6.bit._C12
#define OCCP6_C13 _occp6.bit._C13
#define OCCP6_C14 _occp6.bit._C14
#define OCCP6_C15 _occp6.bit._C15
#define OCCP6_C0 _occp6.bitc._C0
__IO_EXTERN __io OCCP7STR _occp7;  
#define OCCP7 _occp7.word
#define OCCP7_C00 _occp7.bit._C00
#define OCCP7_C01 _occp7.bit._C01
#define OCCP7_C02 _occp7.bit._C02
#define OCCP7_C03 _occp7.bit._C03
#define OCCP7_C04 _occp7.bit._C04
#define OCCP7_C05 _occp7.bit._C05
#define OCCP7_C06 _occp7.bit._C06
#define OCCP7_C07 _occp7.bit._C07
#define OCCP7_C08 _occp7.bit._C08
#define OCCP7_C09 _occp7.bit._C09
#define OCCP7_C10 _occp7.bit._C10
#define OCCP7_C11 _occp7.bit._C11
#define OCCP7_C12 _occp7.bit._C12
#define OCCP7_C13 _occp7.bit._C13
#define OCCP7_C14 _occp7.bit._C14
#define OCCP7_C15 _occp7.bit._C15
#define OCCP7_C0 _occp7.bitc._C0
__IO_EXTERN __io ICS01STR _ics01;  
#define ICS01 _ics01.byte
#define ICS01_EG00 _ics01.bit._EG00
#define ICS01_EG01 _ics01.bit._EG01
#define ICS01_EG10 _ics01.bit._EG10
#define ICS01_EG11 _ics01.bit._EG11
#define ICS01_ICE0 _ics01.bit._ICE0
#define ICS01_ICE1 _ics01.bit._ICE1
#define ICS01_ICP0 _ics01.bit._ICP0
#define ICS01_ICP1 _ics01.bit._ICP1
#define ICS01_EG0 _ics01.bitc._EG0
#define ICS01_EG1 _ics01.bitc._EG1
__IO_EXTERN __io ICE01STR _ice01;  
#define ICE01 _ice01.byte
#define ICE01_IEI0 _ice01.bit._IEI0
#define ICE01_IEI1 _ice01.bit._IEI1
#define ICE01_ICUS0 _ice01.bit._ICUS0
#define ICE01_ICUS1 _ice01.bit._ICUS1
__IO_EXTERN __io IPCP0STR _ipcp0;  
#define IPCP0 _ipcp0.word
#define IPCP0_CP00 _ipcp0.bit._CP00
#define IPCP0_CP01 _ipcp0.bit._CP01
#define IPCP0_CP02 _ipcp0.bit._CP02
#define IPCP0_CP03 _ipcp0.bit._CP03
#define IPCP0_CP04 _ipcp0.bit._CP04
#define IPCP0_CP05 _ipcp0.bit._CP05
#define IPCP0_CP06 _ipcp0.bit._CP06
#define IPCP0_CP07 _ipcp0.bit._CP07
#define IPCP0_CP08 _ipcp0.bit._CP08
#define IPCP0_CP09 _ipcp0.bit._CP09
#define IPCP0_CP10 _ipcp0.bit._CP10
#define IPCP0_CP11 _ipcp0.bit._CP11
#define IPCP0_CP12 _ipcp0.bit._CP12
#define IPCP0_CP13 _ipcp0.bit._CP13
#define IPCP0_CP14 _ipcp0.bit._CP14
#define IPCP0_CP15 _ipcp0.bit._CP15
#define IPCP0_CP0 _ipcp0.bitc._CP0
__IO_EXTERN __io IPCPL0STR _ipcpl0;  
#define IPCPL0 _ipcpl0.byte
#define IPCPL0_CP00 _ipcpl0.bit._CP00
#define IPCPL0_CP01 _ipcpl0.bit._CP01
#define IPCPL0_CP02 _ipcpl0.bit._CP02
#define IPCPL0_CP03 _ipcpl0.bit._CP03
#define IPCPL0_CP04 _ipcpl0.bit._CP04
#define IPCPL0_CP05 _ipcpl0.bit._CP05
#define IPCPL0_CP06 _ipcpl0.bit._CP06
#define IPCPL0_CP07 _ipcpl0.bit._CP07
__IO_EXTERN __io IPCPH0STR _ipcph0;  
#define IPCPH0 _ipcph0.byte
#define IPCPH0_CP08 _ipcph0.bit._CP08
#define IPCPH0_CP09 _ipcph0.bit._CP09
#define IPCPH0_CP10 _ipcph0.bit._CP10
#define IPCPH0_CP11 _ipcph0.bit._CP11
#define IPCPH0_CP12 _ipcph0.bit._CP12
#define IPCPH0_CP13 _ipcph0.bit._CP13
#define IPCPH0_CP14 _ipcph0.bit._CP14
#define IPCPH0_CP15 _ipcph0.bit._CP15
__IO_EXTERN __io IPCP1STR _ipcp1;  
#define IPCP1 _ipcp1.word
#define IPCP1_CP00 _ipcp1.bit._CP00
#define IPCP1_CP01 _ipcp1.bit._CP01
#define IPCP1_CP02 _ipcp1.bit._CP02
#define IPCP1_CP03 _ipcp1.bit._CP03
#define IPCP1_CP04 _ipcp1.bit._CP04
#define IPCP1_CP05 _ipcp1.bit._CP05
#define IPCP1_CP06 _ipcp1.bit._CP06
#define IPCP1_CP07 _ipcp1.bit._CP07
#define IPCP1_CP08 _ipcp1.bit._CP08
#define IPCP1_CP09 _ipcp1.bit._CP09
#define IPCP1_CP10 _ipcp1.bit._CP10
#define IPCP1_CP11 _ipcp1.bit._CP11
#define IPCP1_CP12 _ipcp1.bit._CP12
#define IPCP1_CP13 _ipcp1.bit._CP13
#define IPCP1_CP14 _ipcp1.bit._CP14
#define IPCP1_CP15 _ipcp1.bit._CP15
#define IPCP1_CP0 _ipcp1.bitc._CP0
__IO_EXTERN __io IPCPL1STR _ipcpl1;  
#define IPCPL1 _ipcpl1.byte
#define IPCPL1_CP00 _ipcpl1.bit._CP00
#define IPCPL1_CP01 _ipcpl1.bit._CP01
#define IPCPL1_CP02 _ipcpl1.bit._CP02
#define IPCPL1_CP03 _ipcpl1.bit._CP03
#define IPCPL1_CP04 _ipcpl1.bit._CP04
#define IPCPL1_CP05 _ipcpl1.bit._CP05
#define IPCPL1_CP06 _ipcpl1.bit._CP06
#define IPCPL1_CP07 _ipcpl1.bit._CP07
__IO_EXTERN __io IPCPH1STR _ipcph1;  
#define IPCPH1 _ipcph1.byte
#define IPCPH1_CP08 _ipcph1.bit._CP08
#define IPCPH1_CP09 _ipcph1.bit._CP09
#define IPCPH1_CP10 _ipcph1.bit._CP10
#define IPCPH1_CP11 _ipcph1.bit._CP11
#define IPCPH1_CP12 _ipcph1.bit._CP12
#define IPCPH1_CP13 _ipcph1.bit._CP13
#define IPCPH1_CP14 _ipcph1.bit._CP14
#define IPCPH1_CP15 _ipcph1.bit._CP15
__IO_EXTERN __io ICS23STR _ics23;  
#define ICS23 _ics23.byte
#define ICS23_EG20 _ics23.bit._EG20
#define ICS23_EG21 _ics23.bit._EG21
#define ICS23_EG30 _ics23.bit._EG30
#define ICS23_EG31 _ics23.bit._EG31
#define ICS23_ICE2 _ics23.bit._ICE2
#define ICS23_ICE3 _ics23.bit._ICE3
#define ICS23_ICP2 _ics23.bit._ICP2
#define ICS23_ICP3 _ics23.bit._ICP3
#define ICS23_EG2 _ics23.bitc._EG2
#define ICS23_EG3 _ics23.bitc._EG3
__IO_EXTERN __io ICE23STR _ice23;  
#define ICE23 _ice23.byte
#define ICE23_IEI2 _ice23.bit._IEI2
#define ICE23_IEI3 _ice23.bit._IEI3
__IO_EXTERN __io IPCP2STR _ipcp2;  
#define IPCP2 _ipcp2.word
#define IPCP2_CP00 _ipcp2.bit._CP00
#define IPCP2_CP01 _ipcp2.bit._CP01
#define IPCP2_CP02 _ipcp2.bit._CP02
#define IPCP2_CP03 _ipcp2.bit._CP03
#define IPCP2_CP04 _ipcp2.bit._CP04
#define IPCP2_CP05 _ipcp2.bit._CP05
#define IPCP2_CP06 _ipcp2.bit._CP06
#define IPCP2_CP07 _ipcp2.bit._CP07
#define IPCP2_CP08 _ipcp2.bit._CP08
#define IPCP2_CP09 _ipcp2.bit._CP09
#define IPCP2_CP10 _ipcp2.bit._CP10
#define IPCP2_CP11 _ipcp2.bit._CP11
#define IPCP2_CP12 _ipcp2.bit._CP12
#define IPCP2_CP13 _ipcp2.bit._CP13
#define IPCP2_CP14 _ipcp2.bit._CP14
#define IPCP2_CP15 _ipcp2.bit._CP15
#define IPCP2_CP0 _ipcp2.bitc._CP0
__IO_EXTERN __io IPCPL2STR _ipcpl2;  
#define IPCPL2 _ipcpl2.byte
#define IPCPL2_CP00 _ipcpl2.bit._CP00
#define IPCPL2_CP01 _ipcpl2.bit._CP01
#define IPCPL2_CP02 _ipcpl2.bit._CP02
#define IPCPL2_CP03 _ipcpl2.bit._CP03
#define IPCPL2_CP04 _ipcpl2.bit._CP04
#define IPCPL2_CP05 _ipcpl2.bit._CP05
#define IPCPL2_CP06 _ipcpl2.bit._CP06
#define IPCPL2_CP07 _ipcpl2.bit._CP07
__IO_EXTERN __io IPCPH2STR _ipcph2;  
#define IPCPH2 _ipcph2.byte
#define IPCPH2_CP08 _ipcph2.bit._CP08
#define IPCPH2_CP09 _ipcph2.bit._CP09
#define IPCPH2_CP10 _ipcph2.bit._CP10
#define IPCPH2_CP11 _ipcph2.bit._CP11
#define IPCPH2_CP12 _ipcph2.bit._CP12
#define IPCPH2_CP13 _ipcph2.bit._CP13
#define IPCPH2_CP14 _ipcph2.bit._CP14
#define IPCPH2_CP15 _ipcph2.bit._CP15
__IO_EXTERN __io IPCP3STR _ipcp3;  
#define IPCP3 _ipcp3.word
#define IPCP3_CP00 _ipcp3.bit._CP00
#define IPCP3_CP01 _ipcp3.bit._CP01
#define IPCP3_CP02 _ipcp3.bit._CP02
#define IPCP3_CP03 _ipcp3.bit._CP03
#define IPCP3_CP04 _ipcp3.bit._CP04
#define IPCP3_CP05 _ipcp3.bit._CP05
#define IPCP3_CP06 _ipcp3.bit._CP06
#define IPCP3_CP07 _ipcp3.bit._CP07
#define IPCP3_CP08 _ipcp3.bit._CP08
#define IPCP3_CP09 _ipcp3.bit._CP09
#define IPCP3_CP10 _ipcp3.bit._CP10
#define IPCP3_CP11 _ipcp3.bit._CP11
#define IPCP3_CP12 _ipcp3.bit._CP12
#define IPCP3_CP13 _ipcp3.bit._CP13
#define IPCP3_CP14 _ipcp3.bit._CP14
#define IPCP3_CP15 _ipcp3.bit._CP15
#define IPCP3_CP0 _ipcp3.bitc._CP0
__IO_EXTERN __io IPCPL3STR _ipcpl3;  
#define IPCPL3 _ipcpl3.byte
#define IPCPL3_CP00 _ipcpl3.bit._CP00
#define IPCPL3_CP01 _ipcpl3.bit._CP01
#define IPCPL3_CP02 _ipcpl3.bit._CP02
#define IPCPL3_CP03 _ipcpl3.bit._CP03
#define IPCPL3_CP04 _ipcpl3.bit._CP04
#define IPCPL3_CP05 _ipcpl3.bit._CP05
#define IPCPL3_CP06 _ipcpl3.bit._CP06
#define IPCPL3_CP07 _ipcpl3.bit._CP07
__IO_EXTERN __io IPCPH3STR _ipcph3;  
#define IPCPH3 _ipcph3.byte
#define IPCPH3_CP08 _ipcph3.bit._CP08
#define IPCPH3_CP09 _ipcph3.bit._CP09
#define IPCPH3_CP10 _ipcph3.bit._CP10
#define IPCPH3_CP11 _ipcph3.bit._CP11
#define IPCPH3_CP12 _ipcph3.bit._CP12
#define IPCPH3_CP13 _ipcph3.bit._CP13
#define IPCPH3_CP14 _ipcph3.bit._CP14
#define IPCPH3_CP15 _ipcph3.bit._CP15
__IO_EXTERN __io ICS45STR _ics45;  
#define ICS45 _ics45.byte
#define ICS45_EG40 _ics45.bit._EG40
#define ICS45_EG41 _ics45.bit._EG41
#define ICS45_EG50 _ics45.bit._EG50
#define ICS45_EG51 _ics45.bit._EG51
#define ICS45_ICE4 _ics45.bit._ICE4
#define ICS45_ICE5 _ics45.bit._ICE5
#define ICS45_ICP4 _ics45.bit._ICP4
#define ICS45_ICP5 _ics45.bit._ICP5
#define ICS45_EG4 _ics45.bitc._EG4
#define ICS45_EG5 _ics45.bitc._EG5
__IO_EXTERN __io ICE45STR _ice45;  
#define ICE45 _ice45.byte
#define ICE45_IEI4 _ice45.bit._IEI4
#define ICE45_IEI5 _ice45.bit._IEI5
#define ICE45_ICUS4 _ice45.bit._ICUS4
#define ICE45_ICUS5 _ice45.bit._ICUS5
__IO_EXTERN __io IPCP4STR _ipcp4;  
#define IPCP4 _ipcp4.word
#define IPCP4_CP00 _ipcp4.bit._CP00
#define IPCP4_CP01 _ipcp4.bit._CP01
#define IPCP4_CP02 _ipcp4.bit._CP02
#define IPCP4_CP03 _ipcp4.bit._CP03
#define IPCP4_CP04 _ipcp4.bit._CP04
#define IPCP4_CP05 _ipcp4.bit._CP05
#define IPCP4_CP06 _ipcp4.bit._CP06
#define IPCP4_CP07 _ipcp4.bit._CP07
#define IPCP4_CP08 _ipcp4.bit._CP08
#define IPCP4_CP09 _ipcp4.bit._CP09
#define IPCP4_CP10 _ipcp4.bit._CP10
#define IPCP4_CP11 _ipcp4.bit._CP11
#define IPCP4_CP12 _ipcp4.bit._CP12
#define IPCP4_CP13 _ipcp4.bit._CP13
#define IPCP4_CP14 _ipcp4.bit._CP14
#define IPCP4_CP15 _ipcp4.bit._CP15
#define IPCP4_CP0 _ipcp4.bitc._CP0
__IO_EXTERN __io IPCPL4STR _ipcpl4;  
#define IPCPL4 _ipcpl4.byte
#define IPCPL4_CP00 _ipcpl4.bit._CP00
#define IPCPL4_CP01 _ipcpl4.bit._CP01
#define IPCPL4_CP02 _ipcpl4.bit._CP02
#define IPCPL4_CP03 _ipcpl4.bit._CP03
#define IPCPL4_CP04 _ipcpl4.bit._CP04
#define IPCPL4_CP05 _ipcpl4.bit._CP05
#define IPCPL4_CP06 _ipcpl4.bit._CP06
#define IPCPL4_CP07 _ipcpl4.bit._CP07
__IO_EXTERN __io IPCPH4STR _ipcph4;  
#define IPCPH4 _ipcph4.byte
#define IPCPH4_CP08 _ipcph4.bit._CP08
#define IPCPH4_CP09 _ipcph4.bit._CP09
#define IPCPH4_CP10 _ipcph4.bit._CP10
#define IPCPH4_CP11 _ipcph4.bit._CP11
#define IPCPH4_CP12 _ipcph4.bit._CP12
#define IPCPH4_CP13 _ipcph4.bit._CP13
#define IPCPH4_CP14 _ipcph4.bit._CP14
#define IPCPH4_CP15 _ipcph4.bit._CP15
__IO_EXTERN __io IPCP5STR _ipcp5;  
#define IPCP5 _ipcp5.word
#define IPCP5_CP00 _ipcp5.bit._CP00
#define IPCP5_CP01 _ipcp5.bit._CP01
#define IPCP5_CP02 _ipcp5.bit._CP02
#define IPCP5_CP03 _ipcp5.bit._CP03
#define IPCP5_CP04 _ipcp5.bit._CP04
#define IPCP5_CP05 _ipcp5.bit._CP05
#define IPCP5_CP06 _ipcp5.bit._CP06
#define IPCP5_CP07 _ipcp5.bit._CP07
#define IPCP5_CP08 _ipcp5.bit._CP08
#define IPCP5_CP09 _ipcp5.bit._CP09
#define IPCP5_CP10 _ipcp5.bit._CP10
#define IPCP5_CP11 _ipcp5.bit._CP11
#define IPCP5_CP12 _ipcp5.bit._CP12
#define IPCP5_CP13 _ipcp5.bit._CP13
#define IPCP5_CP14 _ipcp5.bit._CP14
#define IPCP5_CP15 _ipcp5.bit._CP15
#define IPCP5_CP0 _ipcp5.bitc._CP0
__IO_EXTERN __io IPCPL5STR _ipcpl5;  
#define IPCPL5 _ipcpl5.byte
#define IPCPL5_CP00 _ipcpl5.bit._CP00
#define IPCPL5_CP01 _ipcpl5.bit._CP01
#define IPCPL5_CP02 _ipcpl5.bit._CP02
#define IPCPL5_CP03 _ipcpl5.bit._CP03
#define IPCPL5_CP04 _ipcpl5.bit._CP04
#define IPCPL5_CP05 _ipcpl5.bit._CP05
#define IPCPL5_CP06 _ipcpl5.bit._CP06
#define IPCPL5_CP07 _ipcpl5.bit._CP07
__IO_EXTERN __io IPCPH5STR _ipcph5;  
#define IPCPH5 _ipcph5.byte
#define IPCPH5_CP08 _ipcph5.bit._CP08
#define IPCPH5_CP09 _ipcph5.bit._CP09
#define IPCPH5_CP10 _ipcph5.bit._CP10
#define IPCPH5_CP11 _ipcph5.bit._CP11
#define IPCPH5_CP12 _ipcph5.bit._CP12
#define IPCPH5_CP13 _ipcph5.bit._CP13
#define IPCPH5_CP14 _ipcph5.bit._CP14
#define IPCPH5_CP15 _ipcph5.bit._CP15
__IO_EXTERN __io ICS67STR _ics67;  
#define ICS67 _ics67.byte
#define ICS67_EG60 _ics67.bit._EG60
#define ICS67_EG61 _ics67.bit._EG61
#define ICS67_EG70 _ics67.bit._EG70
#define ICS67_EG71 _ics67.bit._EG71
#define ICS67_ICE6 _ics67.bit._ICE6
#define ICS67_ICE7 _ics67.bit._ICE7
#define ICS67_ICP6 _ics67.bit._ICP6
#define ICS67_ICP7 _ics67.bit._ICP7
#define ICS67_EG6 _ics67.bitc._EG6
#define ICS67_EG7 _ics67.bitc._EG7
__IO_EXTERN __io ICE67STR _ice67;  
#define ICE67 _ice67.byte
#define ICE67_IEI6 _ice67.bit._IEI6
#define ICE67_IEI7 _ice67.bit._IEI7
#define ICE67_ICUS6 _ice67.bit._ICUS6
#define ICE67_ICUS7 _ice67.bit._ICUS7
__IO_EXTERN __io IPCP6STR _ipcp6;  
#define IPCP6 _ipcp6.word
#define IPCP6_CP00 _ipcp6.bit._CP00
#define IPCP6_CP01 _ipcp6.bit._CP01
#define IPCP6_CP02 _ipcp6.bit._CP02
#define IPCP6_CP03 _ipcp6.bit._CP03
#define IPCP6_CP04 _ipcp6.bit._CP04
#define IPCP6_CP05 _ipcp6.bit._CP05
#define IPCP6_CP06 _ipcp6.bit._CP06
#define IPCP6_CP07 _ipcp6.bit._CP07
#define IPCP6_CP08 _ipcp6.bit._CP08
#define IPCP6_CP09 _ipcp6.bit._CP09
#define IPCP6_CP10 _ipcp6.bit._CP10
#define IPCP6_CP11 _ipcp6.bit._CP11
#define IPCP6_CP12 _ipcp6.bit._CP12
#define IPCP6_CP13 _ipcp6.bit._CP13
#define IPCP6_CP14 _ipcp6.bit._CP14
#define IPCP6_CP15 _ipcp6.bit._CP15
#define IPCP6_CP0 _ipcp6.bitc._CP0
__IO_EXTERN __io IPCPL6STR _ipcpl6;  
#define IPCPL6 _ipcpl6.byte
#define IPCPL6_CP00 _ipcpl6.bit._CP00
#define IPCPL6_CP01 _ipcpl6.bit._CP01
#define IPCPL6_CP02 _ipcpl6.bit._CP02
#define IPCPL6_CP03 _ipcpl6.bit._CP03
#define IPCPL6_CP04 _ipcpl6.bit._CP04
#define IPCPL6_CP05 _ipcpl6.bit._CP05
#define IPCPL6_CP06 _ipcpl6.bit._CP06
#define IPCPL6_CP07 _ipcpl6.bit._CP07
__IO_EXTERN __io IPCPH6STR _ipcph6;  
#define IPCPH6 _ipcph6.byte
#define IPCPH6_CP08 _ipcph6.bit._CP08
#define IPCPH6_CP09 _ipcph6.bit._CP09
#define IPCPH6_CP10 _ipcph6.bit._CP10
#define IPCPH6_CP11 _ipcph6.bit._CP11
#define IPCPH6_CP12 _ipcph6.bit._CP12
#define IPCPH6_CP13 _ipcph6.bit._CP13
#define IPCPH6_CP14 _ipcph6.bit._CP14
#define IPCPH6_CP15 _ipcph6.bit._CP15
__IO_EXTERN __io IPCP7STR _ipcp7;  
#define IPCP7 _ipcp7.word
#define IPCP7_CP00 _ipcp7.bit._CP00
#define IPCP7_CP01 _ipcp7.bit._CP01
#define IPCP7_CP02 _ipcp7.bit._CP02
#define IPCP7_CP03 _ipcp7.bit._CP03
#define IPCP7_CP04 _ipcp7.bit._CP04
#define IPCP7_CP05 _ipcp7.bit._CP05
#define IPCP7_CP06 _ipcp7.bit._CP06
#define IPCP7_CP07 _ipcp7.bit._CP07
#define IPCP7_CP08 _ipcp7.bit._CP08
#define IPCP7_CP09 _ipcp7.bit._CP09
#define IPCP7_CP10 _ipcp7.bit._CP10
#define IPCP7_CP11 _ipcp7.bit._CP11
#define IPCP7_CP12 _ipcp7.bit._CP12
#define IPCP7_CP13 _ipcp7.bit._CP13
#define IPCP7_CP14 _ipcp7.bit._CP14
#define IPCP7_CP15 _ipcp7.bit._CP15
#define IPCP7_CP0 _ipcp7.bitc._CP0
__IO_EXTERN __io IPCPL7STR _ipcpl7;  
#define IPCPL7 _ipcpl7.byte
#define IPCPL7_CP00 _ipcpl7.bit._CP00
#define IPCPL7_CP01 _ipcpl7.bit._CP01
#define IPCPL7_CP02 _ipcpl7.bit._CP02
#define IPCPL7_CP03 _ipcpl7.bit._CP03
#define IPCPL7_CP04 _ipcpl7.bit._CP04
#define IPCPL7_CP05 _ipcpl7.bit._CP05
#define IPCPL7_CP06 _ipcpl7.bit._CP06
#define IPCPL7_CP07 _ipcpl7.bit._CP07
__IO_EXTERN __io IPCPH7STR _ipcph7;  
#define IPCPH7 _ipcph7.byte
#define IPCPH7_CP08 _ipcph7.bit._CP08
#define IPCPH7_CP09 _ipcph7.bit._CP09
#define IPCPH7_CP10 _ipcph7.bit._CP10
#define IPCPH7_CP11 _ipcph7.bit._CP11
#define IPCPH7_CP12 _ipcph7.bit._CP12
#define IPCPH7_CP13 _ipcph7.bit._CP13
#define IPCPH7_CP14 _ipcph7.bit._CP14
#define IPCPH7_CP15 _ipcph7.bit._CP15
__IO_EXTERN __io ENIR0STR _enir0;  
#define ENIR0 _enir0.byte
#define ENIR0_EN0 _enir0.bit._EN0
#define ENIR0_EN1 _enir0.bit._EN1
#define ENIR0_EN2 _enir0.bit._EN2
#define ENIR0_EN3 _enir0.bit._EN3
#define ENIR0_EN4 _enir0.bit._EN4
#define ENIR0_EN5 _enir0.bit._EN5
#define ENIR0_EN6 _enir0.bit._EN6
#define ENIR0_EN7 _enir0.bit._EN7
__IO_EXTERN __io EIRR0STR _eirr0;  
#define EIRR0 _eirr0.byte
#define EIRR0_ER0 _eirr0.bit._ER0
#define EIRR0_ER1 _eirr0.bit._ER1
#define EIRR0_ER2 _eirr0.bit._ER2
#define EIRR0_ER3 _eirr0.bit._ER3
#define EIRR0_ER4 _eirr0.bit._ER4
#define EIRR0_ER5 _eirr0.bit._ER5
#define EIRR0_ER6 _eirr0.bit._ER6
#define EIRR0_ER7 _eirr0.bit._ER7
__IO_EXTERN __io ELVR0STR _elvr0;  
#define ELVR0 _elvr0.word
#define ELVR0_LA0 _elvr0.bit._LA0
#define ELVR0_LB0 _elvr0.bit._LB0
#define ELVR0_LA1 _elvr0.bit._LA1
#define ELVR0_LB1 _elvr0.bit._LB1
#define ELVR0_LA2 _elvr0.bit._LA2
#define ELVR0_LB2 _elvr0.bit._LB2
#define ELVR0_LA3 _elvr0.bit._LA3
#define ELVR0_LB3 _elvr0.bit._LB3
#define ELVR0_LA4 _elvr0.bit._LA4
#define ELVR0_LB4 _elvr0.bit._LB4
#define ELVR0_LA5 _elvr0.bit._LA5
#define ELVR0_LB5 _elvr0.bit._LB5
#define ELVR0_LA6 _elvr0.bit._LA6
#define ELVR0_LB6 _elvr0.bit._LB6
#define ELVR0_LA7 _elvr0.bit._LA7
#define ELVR0_LB7 _elvr0.bit._LB7
__IO_EXTERN __io ELVRL0STR _elvrl0;  
#define ELVRL0 _elvrl0.byte
#define ELVRL0_LA0 _elvrl0.bit._LA0
#define ELVRL0_LB0 _elvrl0.bit._LB0
#define ELVRL0_LA1 _elvrl0.bit._LA1
#define ELVRL0_LB1 _elvrl0.bit._LB1
#define ELVRL0_LA2 _elvrl0.bit._LA2
#define ELVRL0_LB2 _elvrl0.bit._LB2
#define ELVRL0_LA3 _elvrl0.bit._LA3
#define ELVRL0_LB3 _elvrl0.bit._LB3
__IO_EXTERN __io ELVRH0STR _elvrh0;  
#define ELVRH0 _elvrh0.byte
#define ELVRH0_LA4 _elvrh0.bit._LA4
#define ELVRH0_LB4 _elvrh0.bit._LB4
#define ELVRH0_LA5 _elvrh0.bit._LA5
#define ELVRH0_LB5 _elvrh0.bit._LB5
#define ELVRH0_LA6 _elvrh0.bit._LA6
#define ELVRH0_LB6 _elvrh0.bit._LB6
#define ELVRH0_LA7 _elvrh0.bit._LA7
#define ELVRH0_LB7 _elvrh0.bit._LB7
__IO_EXTERN __io ENIR1STR _enir1;  
#define ENIR1 _enir1.byte
#define ENIR1_EN8 _enir1.bit._EN8
#define ENIR1_EN9 _enir1.bit._EN9
#define ENIR1_EN10 _enir1.bit._EN10
#define ENIR1_EN11 _enir1.bit._EN11
#define ENIR1_EN12 _enir1.bit._EN12
#define ENIR1_EN13 _enir1.bit._EN13
#define ENIR1_EN14 _enir1.bit._EN14
#define ENIR1_EN15 _enir1.bit._EN15
__IO_EXTERN __io EIRR1STR _eirr1;  
#define EIRR1 _eirr1.byte
#define EIRR1_ER8 _eirr1.bit._ER8
#define EIRR1_ER9 _eirr1.bit._ER9
#define EIRR1_ER10 _eirr1.bit._ER10
#define EIRR1_ER11 _eirr1.bit._ER11
#define EIRR1_ER12 _eirr1.bit._ER12
#define EIRR1_ER13 _eirr1.bit._ER13
#define EIRR1_ER14 _eirr1.bit._ER14
#define EIRR1_ER15 _eirr1.bit._ER15
__IO_EXTERN __io ELVR1STR _elvr1;  
#define ELVR1 _elvr1.word
#define ELVR1_LA8 _elvr1.bit._LA8
#define ELVR1_LB8 _elvr1.bit._LB8
#define ELVR1_LA9 _elvr1.bit._LA9
#define ELVR1_LB9 _elvr1.bit._LB9
#define ELVR1_LA10 _elvr1.bit._LA10
#define ELVR1_LB10 _elvr1.bit._LB10
#define ELVR1_LA11 _elvr1.bit._LA11
#define ELVR1_LB11 _elvr1.bit._LB11
#define ELVR1_LA12 _elvr1.bit._LA12
#define ELVR1_LB12 _elvr1.bit._LB12
#define ELVR1_LA13 _elvr1.bit._LA13
#define ELVR1_LB13 _elvr1.bit._LB13
#define ELVR1_LA14 _elvr1.bit._LA14
#define ELVR1_LB14 _elvr1.bit._LB14
#define ELVR1_LA15 _elvr1.bit._LA15
#define ELVR1_LB15 _elvr1.bit._LB15
__IO_EXTERN __io ELVRL1STR _elvrl1;  
#define ELVRL1 _elvrl1.byte
#define ELVRL1_LA8 _elvrl1.bit._LA8
#define ELVRL1_LB8 _elvrl1.bit._LB8
#define ELVRL1_LA9 _elvrl1.bit._LA9
#define ELVRL1_LB9 _elvrl1.bit._LB9
#define ELVRL1_LA10 _elvrl1.bit._LA10
#define ELVRL1_LB10 _elvrl1.bit._LB10
#define ELVRL1_LA11 _elvrl1.bit._LA11
#define ELVRL1_LB11 _elvrl1.bit._LB11
__IO_EXTERN __io ELVRH1STR _elvrh1;  
#define ELVRH1 _elvrh1.byte
#define ELVRH1_LA12 _elvrh1.bit._LA12
#define ELVRH1_LB12 _elvrh1.bit._LB12
#define ELVRH1_LA13 _elvrh1.bit._LA13
#define ELVRH1_LB13 _elvrh1.bit._LB13
#define ELVRH1_LA14 _elvrh1.bit._LA14
#define ELVRH1_LB14 _elvrh1.bit._LB14
#define ELVRH1_LA15 _elvrh1.bit._LA15
#define ELVRH1_LB15 _elvrh1.bit._LB15
__IO_EXTERN __io TMCSR0STR _tmcsr0;  
#define TMCSR0 _tmcsr0.word
#define TMCSR0_TRG _tmcsr0.bit._TRG
#define TMCSR0_CNTE _tmcsr0.bit._CNTE
#define TMCSR0_UF _tmcsr0.bit._UF
#define TMCSR0_INTE _tmcsr0.bit._INTE
#define TMCSR0_RELD _tmcsr0.bit._RELD
#define TMCSR0_OUTL _tmcsr0.bit._OUTL
#define TMCSR0_OUTE _tmcsr0.bit._OUTE
#define TMCSR0_MOD0 _tmcsr0.bit._MOD0
#define TMCSR0_MOD1 _tmcsr0.bit._MOD1
#define TMCSR0_MOD2 _tmcsr0.bit._MOD2
#define TMCSR0_CSL0 _tmcsr0.bit._CSL0
#define TMCSR0_CSL1 _tmcsr0.bit._CSL1
#define TMCSR0_FSEL _tmcsr0.bit._FSEL
#define TMCSR0_CSL _tmcsr0.bitc._CSL
__IO_EXTERN __io TMCSRL0STR _tmcsrl0;  
#define TMCSRL0 _tmcsrl0.byte
#define TMCSRL0_TRG _tmcsrl0.bit._TRG
#define TMCSRL0_CNTE _tmcsrl0.bit._CNTE
#define TMCSRL0_UF _tmcsrl0.bit._UF
#define TMCSRL0_INTE _tmcsrl0.bit._INTE
#define TMCSRL0_RELD _tmcsrl0.bit._RELD
#define TMCSRL0_OUTL _tmcsrl0.bit._OUTL
#define TMCSRL0_OUTE _tmcsrl0.bit._OUTE
#define TMCSRL0_MOD0 _tmcsrl0.bit._MOD0
__IO_EXTERN __io TMCSRH0STR _tmcsrh0;  
#define TMCSRH0 _tmcsrh0.byte
#define TMCSRH0_MOD1 _tmcsrh0.bit._MOD1
#define TMCSRH0_MOD2 _tmcsrh0.bit._MOD2
#define TMCSRH0_CSL0 _tmcsrh0.bit._CSL0
#define TMCSRH0_CSL1 _tmcsrh0.bit._CSL1
#define TMCSRH0_FSEL _tmcsrh0.bit._FSEL
#define TMCSRH0_CSL _tmcsrh0.bitc._CSL
__IO_EXTERN __io IO_WORD _tmrlr0;
#define TMRLR0 _tmrlr0   
__IO_EXTERN __io IO_WORD _tmr0;
#define TMR0 _tmr0   
__IO_EXTERN __io TMCSR1STR _tmcsr1;  
#define TMCSR1 _tmcsr1.word
#define TMCSR1_TRG _tmcsr1.bit._TRG
#define TMCSR1_CNTE _tmcsr1.bit._CNTE
#define TMCSR1_UF _tmcsr1.bit._UF
#define TMCSR1_INTE _tmcsr1.bit._INTE
#define TMCSR1_RELD _tmcsr1.bit._RELD
#define TMCSR1_OUTL _tmcsr1.bit._OUTL
#define TMCSR1_OUTE _tmcsr1.bit._OUTE
#define TMCSR1_MOD0 _tmcsr1.bit._MOD0
#define TMCSR1_MOD1 _tmcsr1.bit._MOD1
#define TMCSR1_MOD2 _tmcsr1.bit._MOD2
#define TMCSR1_CSL0 _tmcsr1.bit._CSL0
#define TMCSR1_CSL1 _tmcsr1.bit._CSL1
#define TMCSR1_FSEL _tmcsr1.bit._FSEL
#define TMCSR1_CSL _tmcsr1.bitc._CSL
__IO_EXTERN __io TMCSRL1STR _tmcsrl1;  
#define TMCSRL1 _tmcsrl1.byte
#define TMCSRL1_TRG _tmcsrl1.bit._TRG
#define TMCSRL1_CNTE _tmcsrl1.bit._CNTE
#define TMCSRL1_UF _tmcsrl1.bit._UF
#define TMCSRL1_INTE _tmcsrl1.bit._INTE
#define TMCSRL1_RELD _tmcsrl1.bit._RELD
#define TMCSRL1_OUTL _tmcsrl1.bit._OUTL
#define TMCSRL1_OUTE _tmcsrl1.bit._OUTE
#define TMCSRL1_MOD0 _tmcsrl1.bit._MOD0
__IO_EXTERN __io TMCSRH1STR _tmcsrh1;  
#define TMCSRH1 _tmcsrh1.byte
#define TMCSRH1_MOD1 _tmcsrh1.bit._MOD1
#define TMCSRH1_MOD2 _tmcsrh1.bit._MOD2
#define TMCSRH1_CSL0 _tmcsrh1.bit._CSL0
#define TMCSRH1_CSL1 _tmcsrh1.bit._CSL1
#define TMCSRH1_FSEL _tmcsrh1.bit._FSEL
#define TMCSRH1_CSL _tmcsrh1.bitc._CSL
__IO_EXTERN __io IO_WORD _tmrlr1;
#define TMRLR1 _tmrlr1   
__IO_EXTERN __io IO_WORD _tmr1;
#define TMR1 _tmr1   
__IO_EXTERN __io TMCSR2STR _tmcsr2;  
#define TMCSR2 _tmcsr2.word
#define TMCSR2_TRG _tmcsr2.bit._TRG
#define TMCSR2_CNTE _tmcsr2.bit._CNTE
#define TMCSR2_UF _tmcsr2.bit._UF
#define TMCSR2_INTE _tmcsr2.bit._INTE
#define TMCSR2_RELD _tmcsr2.bit._RELD
#define TMCSR2_OUTL _tmcsr2.bit._OUTL
#define TMCSR2_OUTE _tmcsr2.bit._OUTE
#define TMCSR2_MOD0 _tmcsr2.bit._MOD0
#define TMCSR2_MOD1 _tmcsr2.bit._MOD1
#define TMCSR2_MOD2 _tmcsr2.bit._MOD2
#define TMCSR2_CSL0 _tmcsr2.bit._CSL0
#define TMCSR2_CSL1 _tmcsr2.bit._CSL1
#define TMCSR2_FSEL _tmcsr2.bit._FSEL
#define TMCSR2_CSL _tmcsr2.bitc._CSL
__IO_EXTERN __io TMCSRL2STR _tmcsrl2;  
#define TMCSRL2 _tmcsrl2.byte
#define TMCSRL2_TRG _tmcsrl2.bit._TRG
#define TMCSRL2_CNTE _tmcsrl2.bit._CNTE
#define TMCSRL2_UF _tmcsrl2.bit._UF
#define TMCSRL2_INTE _tmcsrl2.bit._INTE
#define TMCSRL2_RELD _tmcsrl2.bit._RELD
#define TMCSRL2_OUTL _tmcsrl2.bit._OUTL
#define TMCSRL2_OUTE _tmcsrl2.bit._OUTE
#define TMCSRL2_MOD0 _tmcsrl2.bit._MOD0
__IO_EXTERN __io TMCSRH2STR _tmcsrh2;  
#define TMCSRH2 _tmcsrh2.byte
#define TMCSRH2_MOD1 _tmcsrh2.bit._MOD1
#define TMCSRH2_MOD2 _tmcsrh2.bit._MOD2
#define TMCSRH2_CSL0 _tmcsrh2.bit._CSL0
#define TMCSRH2_CSL1 _tmcsrh2.bit._CSL1
#define TMCSRH2_FSEL _tmcsrh2.bit._FSEL
#define TMCSRH2_CSL _tmcsrh2.bitc._CSL
__IO_EXTERN __io IO_WORD _tmrlr2;
#define TMRLR2 _tmrlr2   
__IO_EXTERN __io IO_WORD _tmr2;
#define TMR2 _tmr2   
__IO_EXTERN __io TMCSR3STR _tmcsr3;  
#define TMCSR3 _tmcsr3.word
#define TMCSR3_TRG _tmcsr3.bit._TRG
#define TMCSR3_CNTE _tmcsr3.bit._CNTE
#define TMCSR3_UF _tmcsr3.bit._UF
#define TMCSR3_INTE _tmcsr3.bit._INTE
#define TMCSR3_RELD _tmcsr3.bit._RELD
#define TMCSR3_OUTL _tmcsr3.bit._OUTL
#define TMCSR3_OUTE _tmcsr3.bit._OUTE
#define TMCSR3_MOD0 _tmcsr3.bit._MOD0
#define TMCSR3_MOD1 _tmcsr3.bit._MOD1
#define TMCSR3_MOD2 _tmcsr3.bit._MOD2
#define TMCSR3_CSL0 _tmcsr3.bit._CSL0
#define TMCSR3_CSL1 _tmcsr3.bit._CSL1
#define TMCSR3_FSEL _tmcsr3.bit._FSEL
#define TMCSR3_CSL _tmcsr3.bitc._CSL
__IO_EXTERN __io TMCSRL3STR _tmcsrl3;  
#define TMCSRL3 _tmcsrl3.byte
#define TMCSRL3_TRG _tmcsrl3.bit._TRG
#define TMCSRL3_CNTE _tmcsrl3.bit._CNTE
#define TMCSRL3_UF _tmcsrl3.bit._UF
#define TMCSRL3_INTE _tmcsrl3.bit._INTE
#define TMCSRL3_RELD _tmcsrl3.bit._RELD
#define TMCSRL3_OUTL _tmcsrl3.bit._OUTL
#define TMCSRL3_OUTE _tmcsrl3.bit._OUTE
#define TMCSRL3_MOD0 _tmcsrl3.bit._MOD0
__IO_EXTERN __io TMCSRH3STR _tmcsrh3;  
#define TMCSRH3 _tmcsrh3.byte
#define TMCSRH3_MOD1 _tmcsrh3.bit._MOD1
#define TMCSRH3_MOD2 _tmcsrh3.bit._MOD2
#define TMCSRH3_CSL0 _tmcsrh3.bit._CSL0
#define TMCSRH3_CSL1 _tmcsrh3.bit._CSL1
#define TMCSRH3_FSEL _tmcsrh3.bit._FSEL
#define TMCSRH3_CSL _tmcsrh3.bitc._CSL
__IO_EXTERN __io IO_WORD _tmrlr3;
#define TMRLR3 _tmrlr3   
__IO_EXTERN __io IO_WORD _tmr3;
#define TMR3 _tmr3   
__IO_EXTERN __io TMCSR6STR _tmcsr6;  
#define TMCSR6 _tmcsr6.word
#define TMCSR6_TRG _tmcsr6.bit._TRG
#define TMCSR6_CNTE _tmcsr6.bit._CNTE
#define TMCSR6_UF _tmcsr6.bit._UF
#define TMCSR6_INTE _tmcsr6.bit._INTE
#define TMCSR6_RELD _tmcsr6.bit._RELD
#define TMCSR6_MOD0 _tmcsr6.bit._MOD0
#define TMCSR6_MOD1 _tmcsr6.bit._MOD1
#define TMCSR6_MOD2 _tmcsr6.bit._MOD2
#define TMCSR6_CSL0 _tmcsr6.bit._CSL0
#define TMCSR6_CSL1 _tmcsr6.bit._CSL1
#define TMCSR6_FSEL _tmcsr6.bit._FSEL
#define TMCSR6_CSL _tmcsr6.bitc._CSL
__IO_EXTERN __io TMCSRL6STR _tmcsrl6;  
#define TMCSRL6 _tmcsrl6.byte
#define TMCSRL6_TRG _tmcsrl6.bit._TRG
#define TMCSRL6_CNTE _tmcsrl6.bit._CNTE
#define TMCSRL6_UF _tmcsrl6.bit._UF
#define TMCSRL6_INTE _tmcsrl6.bit._INTE
#define TMCSRL6_RELD _tmcsrl6.bit._RELD
#define TMCSRL6_MOD0 _tmcsrl6.bit._MOD0
__IO_EXTERN __io TMCSRH6STR _tmcsrh6;  
#define TMCSRH6 _tmcsrh6.byte
#define TMCSRH6_MOD1 _tmcsrh6.bit._MOD1
#define TMCSRH6_MOD2 _tmcsrh6.bit._MOD2
#define TMCSRH6_CSL0 _tmcsrh6.bit._CSL0
#define TMCSRH6_CSL1 _tmcsrh6.bit._CSL1
#define TMCSRH6_FSEL _tmcsrh6.bit._FSEL
#define TMCSRH6_CSL _tmcsrh6.bitc._CSL
__IO_EXTERN __io IO_WORD _tmrlr6;
#define TMRLR6 _tmrlr6   
__IO_EXTERN __io IO_WORD _tmr6;
#define TMR6 _tmr6   
__IO_EXTERN __io GCN10STR _gcn10;  
#define GCN10 _gcn10.word
#define GCN10_TSEL00 _gcn10.bit._TSEL00
#define GCN10_TSEL01 _gcn10.bit._TSEL01
#define GCN10_TSEL02 _gcn10.bit._TSEL02
#define GCN10_TSEL03 _gcn10.bit._TSEL03
#define GCN10_TSEL10 _gcn10.bit._TSEL10
#define GCN10_TSEL11 _gcn10.bit._TSEL11
#define GCN10_TSEL12 _gcn10.bit._TSEL12
#define GCN10_TSEL13 _gcn10.bit._TSEL13
#define GCN10_TSEL20 _gcn10.bit._TSEL20
#define GCN10_TSEL21 _gcn10.bit._TSEL21
#define GCN10_TSEL22 _gcn10.bit._TSEL22
#define GCN10_TSEL23 _gcn10.bit._TSEL23
#define GCN10_TSEL30 _gcn10.bit._TSEL30
#define GCN10_TSEL31 _gcn10.bit._TSEL31
#define GCN10_TSEL32 _gcn10.bit._TSEL32
#define GCN10_TSEL33 _gcn10.bit._TSEL33
#define GCN10_TSEL0 _gcn10.bitc._TSEL0
#define GCN10_TSEL1 _gcn10.bitc._TSEL1
#define GCN10_TSEL2 _gcn10.bitc._TSEL2
#define GCN10_TSEL3 _gcn10.bitc._TSEL3
__IO_EXTERN __io GCN1L0STR _gcn1l0;  
#define GCN1L0 _gcn1l0.byte
#define GCN1L0_TSEL00 _gcn1l0.bit._TSEL00
#define GCN1L0_TSEL01 _gcn1l0.bit._TSEL01
#define GCN1L0_TSEL02 _gcn1l0.bit._TSEL02
#define GCN1L0_TSEL03 _gcn1l0.bit._TSEL03
#define GCN1L0_TSEL10 _gcn1l0.bit._TSEL10
#define GCN1L0_TSEL11 _gcn1l0.bit._TSEL11
#define GCN1L0_TSEL12 _gcn1l0.bit._TSEL12
#define GCN1L0_TSEL13 _gcn1l0.bit._TSEL13
#define GCN1L0_TSEL0 _gcn1l0.bitc._TSEL0
#define GCN1L0_TSEL1 _gcn1l0.bitc._TSEL1
__IO_EXTERN __io GCN1H0STR _gcn1h0;  
#define GCN1H0 _gcn1h0.byte
#define GCN1H0_TSEL20 _gcn1h0.bit._TSEL20
#define GCN1H0_TSEL21 _gcn1h0.bit._TSEL21
#define GCN1H0_TSEL22 _gcn1h0.bit._TSEL22
#define GCN1H0_TSEL23 _gcn1h0.bit._TSEL23
#define GCN1H0_TSEL30 _gcn1h0.bit._TSEL30
#define GCN1H0_TSEL31 _gcn1h0.bit._TSEL31
#define GCN1H0_TSEL32 _gcn1h0.bit._TSEL32
#define GCN1H0_TSEL33 _gcn1h0.bit._TSEL33
#define GCN1H0_TSEL2 _gcn1h0.bitc._TSEL2
#define GCN1H0_TSEL3 _gcn1h0.bitc._TSEL3
__IO_EXTERN __io GCN20STR _gcn20;  
#define GCN20 _gcn20.word
#define GCN20_EN0 _gcn20.bit._EN0
#define GCN20_EN1 _gcn20.bit._EN1
#define GCN20_EN2 _gcn20.bit._EN2
#define GCN20_EN3 _gcn20.bit._EN3
#define GCN20_CKSEL0 _gcn20.bit._CKSEL0
#define GCN20_CKSEL1 _gcn20.bit._CKSEL1
#define GCN20_CKSEL2 _gcn20.bit._CKSEL2
#define GCN20_CKSEL3 _gcn20.bit._CKSEL3
#define GCN20_EN _gcn20.bitc._EN
#define GCN20_CKSEL _gcn20.bitc._CKSEL
__IO_EXTERN __io GCN2L0STR _gcn2l0;  
#define GCN2L0 _gcn2l0.byte
#define GCN2L0_EN0 _gcn2l0.bit._EN0
#define GCN2L0_EN1 _gcn2l0.bit._EN1
#define GCN2L0_EN2 _gcn2l0.bit._EN2
#define GCN2L0_EN3 _gcn2l0.bit._EN3
#define GCN2L0_EN _gcn2l0.bitc._EN
__IO_EXTERN __io GCN2H0STR _gcn2h0;  
#define GCN2H0 _gcn2h0.byte
#define GCN2H0_CKSEL0 _gcn2h0.bit._CKSEL0
#define GCN2H0_CKSEL1 _gcn2h0.bit._CKSEL1
#define GCN2H0_CKSEL2 _gcn2h0.bit._CKSEL2
#define GCN2H0_CKSEL3 _gcn2h0.bit._CKSEL3
#define GCN2H0_CKSEL _gcn2h0.bitc._CKSEL
__IO_EXTERN __io PTMR0STR _ptmr0;  
#define PTMR0 _ptmr0.word
#define PTMR0_D0 _ptmr0.bit._D0
#define PTMR0_D1 _ptmr0.bit._D1
#define PTMR0_D2 _ptmr0.bit._D2
#define PTMR0_D3 _ptmr0.bit._D3
#define PTMR0_D4 _ptmr0.bit._D4
#define PTMR0_D5 _ptmr0.bit._D5
#define PTMR0_D6 _ptmr0.bit._D6
#define PTMR0_D7 _ptmr0.bit._D7
#define PTMR0_D8 _ptmr0.bit._D8
#define PTMR0_D9 _ptmr0.bit._D9
#define PTMR0_D10 _ptmr0.bit._D10
#define PTMR0_D11 _ptmr0.bit._D11
#define PTMR0_D12 _ptmr0.bit._D12
#define PTMR0_D13 _ptmr0.bit._D13
#define PTMR0_D14 _ptmr0.bit._D14
#define PTMR0_D15 _ptmr0.bit._D15
#define PTMR0_D _ptmr0.bitc._D
__IO_EXTERN __io PCSR0STR _pcsr0;  
#define PCSR0 _pcsr0.word
#define PCSR0_D0 _pcsr0.bit._D0
#define PCSR0_D1 _pcsr0.bit._D1
#define PCSR0_D2 _pcsr0.bit._D2
#define PCSR0_D3 _pcsr0.bit._D3
#define PCSR0_D4 _pcsr0.bit._D4
#define PCSR0_D5 _pcsr0.bit._D5
#define PCSR0_D6 _pcsr0.bit._D6
#define PCSR0_D7 _pcsr0.bit._D7
#define PCSR0_D8 _pcsr0.bit._D8
#define PCSR0_D9 _pcsr0.bit._D9
#define PCSR0_D10 _pcsr0.bit._D10
#define PCSR0_D11 _pcsr0.bit._D11
#define PCSR0_D12 _pcsr0.bit._D12
#define PCSR0_D13 _pcsr0.bit._D13
#define PCSR0_D14 _pcsr0.bit._D14
#define PCSR0_D15 _pcsr0.bit._D15
#define PCSR0_D _pcsr0.bitc._D
__IO_EXTERN __io PDUT0STR _pdut0;  
#define PDUT0 _pdut0.word
#define PDUT0_D0 _pdut0.bit._D0
#define PDUT0_D1 _pdut0.bit._D1
#define PDUT0_D2 _pdut0.bit._D2
#define PDUT0_D3 _pdut0.bit._D3
#define PDUT0_D4 _pdut0.bit._D4
#define PDUT0_D5 _pdut0.bit._D5
#define PDUT0_D6 _pdut0.bit._D6
#define PDUT0_D7 _pdut0.bit._D7
#define PDUT0_D8 _pdut0.bit._D8
#define PDUT0_D9 _pdut0.bit._D9
#define PDUT0_D10 _pdut0.bit._D10
#define PDUT0_D11 _pdut0.bit._D11
#define PDUT0_D12 _pdut0.bit._D12
#define PDUT0_D13 _pdut0.bit._D13
#define PDUT0_D14 _pdut0.bit._D14
#define PDUT0_D15 _pdut0.bit._D15
#define PDUT0_D _pdut0.bitc._D
__IO_EXTERN __io PCN0STR _pcn0;  
#define PCN0 _pcn0.word
#define PCN0_OSEL _pcn0.bit._OSEL
#define PCN0_OE _pcn0.bit._OE
#define PCN0_IRS0 _pcn0.bit._IRS0
#define PCN0_IRS1 _pcn0.bit._IRS1
#define PCN0_IRQF _pcn0.bit._IRQF
#define PCN0_IREN _pcn0.bit._IREN
#define PCN0_EGS0 _pcn0.bit._EGS0
#define PCN0_EGS1 _pcn0.bit._EGS1
#define PCN0_PGMS _pcn0.bit._PGMS
#define PCN0_CKS0 _pcn0.bit._CKS0
#define PCN0_CKS1 _pcn0.bit._CKS1
#define PCN0_RTRG _pcn0.bit._RTRG
#define PCN0_MDSE _pcn0.bit._MDSE
#define PCN0_STGR _pcn0.bit._STGR
#define PCN0_CNTE _pcn0.bit._CNTE
#define PCN0_IRS _pcn0.bitc._IRS
#define PCN0_EGS _pcn0.bitc._EGS
#define PCN0_CKS _pcn0.bitc._CKS
__IO_EXTERN __io PCNL0STR _pcnl0;  
#define PCNL0 _pcnl0.byte
#define PCNL0_OSEL _pcnl0.bit._OSEL
#define PCNL0_OE _pcnl0.bit._OE
#define PCNL0_IRS0 _pcnl0.bit._IRS0
#define PCNL0_IRS1 _pcnl0.bit._IRS1
#define PCNL0_IRQF _pcnl0.bit._IRQF
#define PCNL0_IREN _pcnl0.bit._IREN
#define PCNL0_EGS0 _pcnl0.bit._EGS0
#define PCNL0_EGS1 _pcnl0.bit._EGS1
#define PCNL0_IRS _pcnl0.bitc._IRS
#define PCNL0_EGS _pcnl0.bitc._EGS
__IO_EXTERN __io PCNH0STR _pcnh0;  
#define PCNH0 _pcnh0.byte
#define PCNH0_PGMS _pcnh0.bit._PGMS
#define PCNH0_CKS0 _pcnh0.bit._CKS0
#define PCNH0_CKS1 _pcnh0.bit._CKS1
#define PCNH0_RTRG _pcnh0.bit._RTRG
#define PCNH0_MDSE _pcnh0.bit._MDSE
#define PCNH0_STGR _pcnh0.bit._STGR
#define PCNH0_CNTE _pcnh0.bit._CNTE
#define PCNH0_CKS _pcnh0.bitc._CKS
__IO_EXTERN __io PTMR1STR _ptmr1;  
#define PTMR1 _ptmr1.word
#define PTMR1_D0 _ptmr1.bit._D0
#define PTMR1_D1 _ptmr1.bit._D1
#define PTMR1_D2 _ptmr1.bit._D2
#define PTMR1_D3 _ptmr1.bit._D3
#define PTMR1_D4 _ptmr1.bit._D4
#define PTMR1_D5 _ptmr1.bit._D5
#define PTMR1_D6 _ptmr1.bit._D6
#define PTMR1_D7 _ptmr1.bit._D7
#define PTMR1_D8 _ptmr1.bit._D8
#define PTMR1_D9 _ptmr1.bit._D9
#define PTMR1_D10 _ptmr1.bit._D10
#define PTMR1_D11 _ptmr1.bit._D11
#define PTMR1_D12 _ptmr1.bit._D12
#define PTMR1_D13 _ptmr1.bit._D13
#define PTMR1_D14 _ptmr1.bit._D14
#define PTMR1_D15 _ptmr1.bit._D15
#define PTMR1_D _ptmr1.bitc._D
__IO_EXTERN __io PCSR1STR _pcsr1;  
#define PCSR1 _pcsr1.word
#define PCSR1_D0 _pcsr1.bit._D0
#define PCSR1_D1 _pcsr1.bit._D1
#define PCSR1_D2 _pcsr1.bit._D2
#define PCSR1_D3 _pcsr1.bit._D3
#define PCSR1_D4 _pcsr1.bit._D4
#define PCSR1_D5 _pcsr1.bit._D5
#define PCSR1_D6 _pcsr1.bit._D6
#define PCSR1_D7 _pcsr1.bit._D7
#define PCSR1_D8 _pcsr1.bit._D8
#define PCSR1_D9 _pcsr1.bit._D9
#define PCSR1_D10 _pcsr1.bit._D10
#define PCSR1_D11 _pcsr1.bit._D11
#define PCSR1_D12 _pcsr1.bit._D12
#define PCSR1_D13 _pcsr1.bit._D13
#define PCSR1_D14 _pcsr1.bit._D14
#define PCSR1_D15 _pcsr1.bit._D15
#define PCSR1_D _pcsr1.bitc._D
__IO_EXTERN __io PDUT1STR _pdut1;  
#define PDUT1 _pdut1.word
#define PDUT1_D0 _pdut1.bit._D0
#define PDUT1_D1 _pdut1.bit._D1
#define PDUT1_D2 _pdut1.bit._D2
#define PDUT1_D3 _pdut1.bit._D3
#define PDUT1_D4 _pdut1.bit._D4
#define PDUT1_D5 _pdut1.bit._D5
#define PDUT1_D6 _pdut1.bit._D6
#define PDUT1_D7 _pdut1.bit._D7
#define PDUT1_D8 _pdut1.bit._D8
#define PDUT1_D9 _pdut1.bit._D9
#define PDUT1_D10 _pdut1.bit._D10
#define PDUT1_D11 _pdut1.bit._D11
#define PDUT1_D12 _pdut1.bit._D12
#define PDUT1_D13 _pdut1.bit._D13
#define PDUT1_D14 _pdut1.bit._D14
#define PDUT1_D15 _pdut1.bit._D15
#define PDUT1_D _pdut1.bitc._D
__IO_EXTERN __io PCN1STR _pcn1;  
#define PCN1 _pcn1.word
#define PCN1_OSEL _pcn1.bit._OSEL
#define PCN1_OE _pcn1.bit._OE
#define PCN1_IRS0 _pcn1.bit._IRS0
#define PCN1_IRS1 _pcn1.bit._IRS1
#define PCN1_IRQF _pcn1.bit._IRQF
#define PCN1_IREN _pcn1.bit._IREN
#define PCN1_EGS0 _pcn1.bit._EGS0
#define PCN1_EGS1 _pcn1.bit._EGS1
#define PCN1_PGMS _pcn1.bit._PGMS
#define PCN1_CKS0 _pcn1.bit._CKS0
#define PCN1_CKS1 _pcn1.bit._CKS1
#define PCN1_RTRG _pcn1.bit._RTRG
#define PCN1_MDSE _pcn1.bit._MDSE
#define PCN1_STGR _pcn1.bit._STGR
#define PCN1_CNTE _pcn1.bit._CNTE
#define PCN1_IRS _pcn1.bitc._IRS
#define PCN1_EGS _pcn1.bitc._EGS
#define PCN1_CKS _pcn1.bitc._CKS
__IO_EXTERN __io PCNL1STR _pcnl1;  
#define PCNL1 _pcnl1.byte
#define PCNL1_OSEL _pcnl1.bit._OSEL
#define PCNL1_OE _pcnl1.bit._OE
#define PCNL1_IRS0 _pcnl1.bit._IRS0
#define PCNL1_IRS1 _pcnl1.bit._IRS1
#define PCNL1_IRQF _pcnl1.bit._IRQF
#define PCNL1_IREN _pcnl1.bit._IREN
#define PCNL1_EGS0 _pcnl1.bit._EGS0
#define PCNL1_EGS1 _pcnl1.bit._EGS1
#define PCNL1_IRS _pcnl1.bitc._IRS
#define PCNL1_EGS _pcnl1.bitc._EGS
__IO_EXTERN __io PCNH1STR _pcnh1;  
#define PCNH1 _pcnh1.byte
#define PCNH1_PGMS _pcnh1.bit._PGMS
#define PCNH1_CKS0 _pcnh1.bit._CKS0
#define PCNH1_CKS1 _pcnh1.bit._CKS1
#define PCNH1_RTRG _pcnh1.bit._RTRG
#define PCNH1_MDSE _pcnh1.bit._MDSE
#define PCNH1_STGR _pcnh1.bit._STGR
#define PCNH1_CNTE _pcnh1.bit._CNTE
#define PCNH1_CKS _pcnh1.bitc._CKS
__IO_EXTERN __io PTMR2STR _ptmr2;  
#define PTMR2 _ptmr2.word
#define PTMR2_D0 _ptmr2.bit._D0
#define PTMR2_D1 _ptmr2.bit._D1
#define PTMR2_D2 _ptmr2.bit._D2
#define PTMR2_D3 _ptmr2.bit._D3
#define PTMR2_D4 _ptmr2.bit._D4
#define PTMR2_D5 _ptmr2.bit._D5
#define PTMR2_D6 _ptmr2.bit._D6
#define PTMR2_D7 _ptmr2.bit._D7
#define PTMR2_D8 _ptmr2.bit._D8
#define PTMR2_D9 _ptmr2.bit._D9
#define PTMR2_D10 _ptmr2.bit._D10
#define PTMR2_D11 _ptmr2.bit._D11
#define PTMR2_D12 _ptmr2.bit._D12
#define PTMR2_D13 _ptmr2.bit._D13
#define PTMR2_D14 _ptmr2.bit._D14
#define PTMR2_D15 _ptmr2.bit._D15
#define PTMR2_D _ptmr2.bitc._D
__IO_EXTERN __io PCSR2STR _pcsr2;  
#define PCSR2 _pcsr2.word
#define PCSR2_D0 _pcsr2.bit._D0
#define PCSR2_D1 _pcsr2.bit._D1
#define PCSR2_D2 _pcsr2.bit._D2
#define PCSR2_D3 _pcsr2.bit._D3
#define PCSR2_D4 _pcsr2.bit._D4
#define PCSR2_D5 _pcsr2.bit._D5
#define PCSR2_D6 _pcsr2.bit._D6
#define PCSR2_D7 _pcsr2.bit._D7
#define PCSR2_D8 _pcsr2.bit._D8
#define PCSR2_D9 _pcsr2.bit._D9
#define PCSR2_D10 _pcsr2.bit._D10
#define PCSR2_D11 _pcsr2.bit._D11
#define PCSR2_D12 _pcsr2.bit._D12
#define PCSR2_D13 _pcsr2.bit._D13
#define PCSR2_D14 _pcsr2.bit._D14
#define PCSR2_D15 _pcsr2.bit._D15
#define PCSR2_D _pcsr2.bitc._D
__IO_EXTERN __io PDUT2STR _pdut2;  
#define PDUT2 _pdut2.word
#define PDUT2_D0 _pdut2.bit._D0
#define PDUT2_D1 _pdut2.bit._D1
#define PDUT2_D2 _pdut2.bit._D2
#define PDUT2_D3 _pdut2.bit._D3
#define PDUT2_D4 _pdut2.bit._D4
#define PDUT2_D5 _pdut2.bit._D5
#define PDUT2_D6 _pdut2.bit._D6
#define PDUT2_D7 _pdut2.bit._D7
#define PDUT2_D8 _pdut2.bit._D8
#define PDUT2_D9 _pdut2.bit._D9
#define PDUT2_D10 _pdut2.bit._D10
#define PDUT2_D11 _pdut2.bit._D11
#define PDUT2_D12 _pdut2.bit._D12
#define PDUT2_D13 _pdut2.bit._D13
#define PDUT2_D14 _pdut2.bit._D14
#define PDUT2_D15 _pdut2.bit._D15
#define PDUT2_D _pdut2.bitc._D
__IO_EXTERN __io PCN2STR _pcn2;  
#define PCN2 _pcn2.word
#define PCN2_OSEL _pcn2.bit._OSEL
#define PCN2_OE _pcn2.bit._OE
#define PCN2_IRS0 _pcn2.bit._IRS0
#define PCN2_IRS1 _pcn2.bit._IRS1
#define PCN2_IRQF _pcn2.bit._IRQF
#define PCN2_IREN _pcn2.bit._IREN
#define PCN2_EGS0 _pcn2.bit._EGS0
#define PCN2_EGS1 _pcn2.bit._EGS1
#define PCN2_PGMS _pcn2.bit._PGMS
#define PCN2_CKS0 _pcn2.bit._CKS0
#define PCN2_CKS1 _pcn2.bit._CKS1
#define PCN2_RTRG _pcn2.bit._RTRG
#define PCN2_MDSE _pcn2.bit._MDSE
#define PCN2_STGR _pcn2.bit._STGR
#define PCN2_CNTE _pcn2.bit._CNTE
#define PCN2_IRS _pcn2.bitc._IRS
#define PCN2_EGS _pcn2.bitc._EGS
#define PCN2_CKS _pcn2.bitc._CKS
__IO_EXTERN __io PCNL2STR _pcnl2;  
#define PCNL2 _pcnl2.byte
#define PCNL2_OSEL _pcnl2.bit._OSEL
#define PCNL2_OE _pcnl2.bit._OE
#define PCNL2_IRS0 _pcnl2.bit._IRS0
#define PCNL2_IRS1 _pcnl2.bit._IRS1
#define PCNL2_IRQF _pcnl2.bit._IRQF
#define PCNL2_IREN _pcnl2.bit._IREN
#define PCNL2_EGS0 _pcnl2.bit._EGS0
#define PCNL2_EGS1 _pcnl2.bit._EGS1
#define PCNL2_IRS _pcnl2.bitc._IRS
#define PCNL2_EGS _pcnl2.bitc._EGS
__IO_EXTERN __io PCNH2STR _pcnh2;  
#define PCNH2 _pcnh2.byte
#define PCNH2_PGMS _pcnh2.bit._PGMS
#define PCNH2_CKS0 _pcnh2.bit._CKS0
#define PCNH2_CKS1 _pcnh2.bit._CKS1
#define PCNH2_RTRG _pcnh2.bit._RTRG
#define PCNH2_MDSE _pcnh2.bit._MDSE
#define PCNH2_STGR _pcnh2.bit._STGR
#define PCNH2_CNTE _pcnh2.bit._CNTE
#define PCNH2_CKS _pcnh2.bitc._CKS
__IO_EXTERN __io PTMR3STR _ptmr3;  
#define PTMR3 _ptmr3.word
#define PTMR3_D0 _ptmr3.bit._D0
#define PTMR3_D1 _ptmr3.bit._D1
#define PTMR3_D2 _ptmr3.bit._D2
#define PTMR3_D3 _ptmr3.bit._D3
#define PTMR3_D4 _ptmr3.bit._D4
#define PTMR3_D5 _ptmr3.bit._D5
#define PTMR3_D6 _ptmr3.bit._D6
#define PTMR3_D7 _ptmr3.bit._D7
#define PTMR3_D8 _ptmr3.bit._D8
#define PTMR3_D9 _ptmr3.bit._D9
#define PTMR3_D10 _ptmr3.bit._D10
#define PTMR3_D11 _ptmr3.bit._D11
#define PTMR3_D12 _ptmr3.bit._D12
#define PTMR3_D13 _ptmr3.bit._D13
#define PTMR3_D14 _ptmr3.bit._D14
#define PTMR3_D15 _ptmr3.bit._D15
#define PTMR3_D _ptmr3.bitc._D
__IO_EXTERN __io PCSR3STR _pcsr3;  
#define PCSR3 _pcsr3.word
#define PCSR3_D0 _pcsr3.bit._D0
#define PCSR3_D1 _pcsr3.bit._D1
#define PCSR3_D2 _pcsr3.bit._D2
#define PCSR3_D3 _pcsr3.bit._D3
#define PCSR3_D4 _pcsr3.bit._D4
#define PCSR3_D5 _pcsr3.bit._D5
#define PCSR3_D6 _pcsr3.bit._D6
#define PCSR3_D7 _pcsr3.bit._D7
#define PCSR3_D8 _pcsr3.bit._D8
#define PCSR3_D9 _pcsr3.bit._D9
#define PCSR3_D10 _pcsr3.bit._D10
#define PCSR3_D11 _pcsr3.bit._D11
#define PCSR3_D12 _pcsr3.bit._D12
#define PCSR3_D13 _pcsr3.bit._D13
#define PCSR3_D14 _pcsr3.bit._D14
#define PCSR3_D15 _pcsr3.bit._D15
#define PCSR3_D _pcsr3.bitc._D
__IO_EXTERN __io PDUT3STR _pdut3;  
#define PDUT3 _pdut3.word
#define PDUT3_D0 _pdut3.bit._D0
#define PDUT3_D1 _pdut3.bit._D1
#define PDUT3_D2 _pdut3.bit._D2
#define PDUT3_D3 _pdut3.bit._D3
#define PDUT3_D4 _pdut3.bit._D4
#define PDUT3_D5 _pdut3.bit._D5
#define PDUT3_D6 _pdut3.bit._D6
#define PDUT3_D7 _pdut3.bit._D7
#define PDUT3_D8 _pdut3.bit._D8
#define PDUT3_D9 _pdut3.bit._D9
#define PDUT3_D10 _pdut3.bit._D10
#define PDUT3_D11 _pdut3.bit._D11
#define PDUT3_D12 _pdut3.bit._D12
#define PDUT3_D13 _pdut3.bit._D13
#define PDUT3_D14 _pdut3.bit._D14
#define PDUT3_D15 _pdut3.bit._D15
#define PDUT3_D _pdut3.bitc._D
__IO_EXTERN __io PCN3STR _pcn3;  
#define PCN3 _pcn3.word
#define PCN3_OSEL _pcn3.bit._OSEL
#define PCN3_OE _pcn3.bit._OE
#define PCN3_IRS0 _pcn3.bit._IRS0
#define PCN3_IRS1 _pcn3.bit._IRS1
#define PCN3_IRQF _pcn3.bit._IRQF
#define PCN3_IREN _pcn3.bit._IREN
#define PCN3_EGS0 _pcn3.bit._EGS0
#define PCN3_EGS1 _pcn3.bit._EGS1
#define PCN3_PGMS _pcn3.bit._PGMS
#define PCN3_CKS0 _pcn3.bit._CKS0
#define PCN3_CKS1 _pcn3.bit._CKS1
#define PCN3_RTRG _pcn3.bit._RTRG
#define PCN3_MDSE _pcn3.bit._MDSE
#define PCN3_STGR _pcn3.bit._STGR
#define PCN3_CNTE _pcn3.bit._CNTE
#define PCN3_IRS _pcn3.bitc._IRS
#define PCN3_EGS _pcn3.bitc._EGS
#define PCN3_CKS _pcn3.bitc._CKS
__IO_EXTERN __io PCNL3STR _pcnl3;  
#define PCNL3 _pcnl3.byte
#define PCNL3_OSEL _pcnl3.bit._OSEL
#define PCNL3_OE _pcnl3.bit._OE
#define PCNL3_IRS0 _pcnl3.bit._IRS0
#define PCNL3_IRS1 _pcnl3.bit._IRS1
#define PCNL3_IRQF _pcnl3.bit._IRQF
#define PCNL3_IREN _pcnl3.bit._IREN
#define PCNL3_EGS0 _pcnl3.bit._EGS0
#define PCNL3_EGS1 _pcnl3.bit._EGS1
#define PCNL3_IRS _pcnl3.bitc._IRS
#define PCNL3_EGS _pcnl3.bitc._EGS
__IO_EXTERN __io PCNH3STR _pcnh3;  
#define PCNH3 _pcnh3.byte
#define PCNH3_PGMS _pcnh3.bit._PGMS
#define PCNH3_CKS0 _pcnh3.bit._CKS0
#define PCNH3_CKS1 _pcnh3.bit._CKS1
#define PCNH3_RTRG _pcnh3.bit._RTRG
#define PCNH3_MDSE _pcnh3.bit._MDSE
#define PCNH3_STGR _pcnh3.bit._STGR
#define PCNH3_CNTE _pcnh3.bit._CNTE
#define PCNH3_CKS _pcnh3.bitc._CKS
__IO_EXTERN __io GCN11STR _gcn11;  
#define GCN11 _gcn11.word
#define GCN11_TSEL00 _gcn11.bit._TSEL00
#define GCN11_TSEL01 _gcn11.bit._TSEL01
#define GCN11_TSEL02 _gcn11.bit._TSEL02
#define GCN11_TSEL03 _gcn11.bit._TSEL03
#define GCN11_TSEL10 _gcn11.bit._TSEL10
#define GCN11_TSEL11 _gcn11.bit._TSEL11
#define GCN11_TSEL12 _gcn11.bit._TSEL12
#define GCN11_TSEL13 _gcn11.bit._TSEL13
#define GCN11_TSEL20 _gcn11.bit._TSEL20
#define GCN11_TSEL21 _gcn11.bit._TSEL21
#define GCN11_TSEL22 _gcn11.bit._TSEL22
#define GCN11_TSEL23 _gcn11.bit._TSEL23
#define GCN11_TSEL30 _gcn11.bit._TSEL30
#define GCN11_TSEL31 _gcn11.bit._TSEL31
#define GCN11_TSEL32 _gcn11.bit._TSEL32
#define GCN11_TSEL33 _gcn11.bit._TSEL33
#define GCN11_TSEL0 _gcn11.bitc._TSEL0
#define GCN11_TSEL1 _gcn11.bitc._TSEL1
#define GCN11_TSEL2 _gcn11.bitc._TSEL2
#define GCN11_TSEL3 _gcn11.bitc._TSEL3
__IO_EXTERN __io GCN1L1STR _gcn1l1;  
#define GCN1L1 _gcn1l1.byte
#define GCN1L1_TSEL00 _gcn1l1.bit._TSEL00
#define GCN1L1_TSEL01 _gcn1l1.bit._TSEL01
#define GCN1L1_TSEL02 _gcn1l1.bit._TSEL02
#define GCN1L1_TSEL03 _gcn1l1.bit._TSEL03
#define GCN1L1_TSEL10 _gcn1l1.bit._TSEL10
#define GCN1L1_TSEL11 _gcn1l1.bit._TSEL11
#define GCN1L1_TSEL12 _gcn1l1.bit._TSEL12
#define GCN1L1_TSEL13 _gcn1l1.bit._TSEL13
#define GCN1L1_TSEL0 _gcn1l1.bitc._TSEL0
#define GCN1L1_TSEL1 _gcn1l1.bitc._TSEL1
__IO_EXTERN __io GCN1H1STR _gcn1h1;  
#define GCN1H1 _gcn1h1.byte
#define GCN1H1_TSEL20 _gcn1h1.bit._TSEL20
#define GCN1H1_TSEL21 _gcn1h1.bit._TSEL21
#define GCN1H1_TSEL22 _gcn1h1.bit._TSEL22
#define GCN1H1_TSEL23 _gcn1h1.bit._TSEL23
#define GCN1H1_TSEL30 _gcn1h1.bit._TSEL30
#define GCN1H1_TSEL31 _gcn1h1.bit._TSEL31
#define GCN1H1_TSEL32 _gcn1h1.bit._TSEL32
#define GCN1H1_TSEL33 _gcn1h1.bit._TSEL33
#define GCN1H1_TSEL2 _gcn1h1.bitc._TSEL2
#define GCN1H1_TSEL3 _gcn1h1.bitc._TSEL3
__IO_EXTERN __io GCN21STR _gcn21;  
#define GCN21 _gcn21.word
#define GCN21_EN0 _gcn21.bit._EN0
#define GCN21_EN1 _gcn21.bit._EN1
#define GCN21_EN2 _gcn21.bit._EN2
#define GCN21_EN3 _gcn21.bit._EN3
#define GCN21_CKSEL0 _gcn21.bit._CKSEL0
#define GCN21_CKSEL1 _gcn21.bit._CKSEL1
#define GCN21_CKSEL2 _gcn21.bit._CKSEL2
#define GCN21_CKSEL3 _gcn21.bit._CKSEL3
#define GCN21_CKSEL _gcn21.bitc._CKSEL
__IO_EXTERN __io GCN2L1STR _gcn2l1;  
#define GCN2L1 _gcn2l1.byte
#define GCN2L1_EN0 _gcn2l1.bit._EN0
#define GCN2L1_EN1 _gcn2l1.bit._EN1
#define GCN2L1_EN2 _gcn2l1.bit._EN2
#define GCN2L1_EN3 _gcn2l1.bit._EN3
__IO_EXTERN __io GCN2H1STR _gcn2h1;  
#define GCN2H1 _gcn2h1.byte
#define GCN2H1_CKSEL0 _gcn2h1.bit._CKSEL0
#define GCN2H1_CKSEL1 _gcn2h1.bit._CKSEL1
#define GCN2H1_CKSEL2 _gcn2h1.bit._CKSEL2
#define GCN2H1_CKSEL3 _gcn2h1.bit._CKSEL3
#define GCN2H1_CKSEL _gcn2h1.bitc._CKSEL
__IO_EXTERN __io PTMR4STR _ptmr4;  
#define PTMR4 _ptmr4.word
#define PTMR4_D0 _ptmr4.bit._D0
#define PTMR4_D1 _ptmr4.bit._D1
#define PTMR4_D2 _ptmr4.bit._D2
#define PTMR4_D3 _ptmr4.bit._D3
#define PTMR4_D4 _ptmr4.bit._D4
#define PTMR4_D5 _ptmr4.bit._D5
#define PTMR4_D6 _ptmr4.bit._D6
#define PTMR4_D7 _ptmr4.bit._D7
#define PTMR4_D8 _ptmr4.bit._D8
#define PTMR4_D9 _ptmr4.bit._D9
#define PTMR4_D10 _ptmr4.bit._D10
#define PTMR4_D11 _ptmr4.bit._D11
#define PTMR4_D12 _ptmr4.bit._D12
#define PTMR4_D13 _ptmr4.bit._D13
#define PTMR4_D14 _ptmr4.bit._D14
#define PTMR4_D15 _ptmr4.bit._D15
#define PTMR4_D _ptmr4.bitc._D
__IO_EXTERN __io PCSR4STR _pcsr4;  
#define PCSR4 _pcsr4.word
#define PCSR4_D0 _pcsr4.bit._D0
#define PCSR4_D1 _pcsr4.bit._D1
#define PCSR4_D2 _pcsr4.bit._D2
#define PCSR4_D3 _pcsr4.bit._D3
#define PCSR4_D4 _pcsr4.bit._D4
#define PCSR4_D5 _pcsr4.bit._D5
#define PCSR4_D6 _pcsr4.bit._D6
#define PCSR4_D7 _pcsr4.bit._D7
#define PCSR4_D8 _pcsr4.bit._D8
#define PCSR4_D9 _pcsr4.bit._D9
#define PCSR4_D10 _pcsr4.bit._D10
#define PCSR4_D11 _pcsr4.bit._D11
#define PCSR4_D12 _pcsr4.bit._D12
#define PCSR4_D13 _pcsr4.bit._D13
#define PCSR4_D14 _pcsr4.bit._D14
#define PCSR4_D15 _pcsr4.bit._D15
#define PCSR4_D _pcsr4.bitc._D
__IO_EXTERN __io PDUT4STR _pdut4;  
#define PDUT4 _pdut4.word
#define PDUT4_D0 _pdut4.bit._D0
#define PDUT4_D1 _pdut4.bit._D1
#define PDUT4_D2 _pdut4.bit._D2
#define PDUT4_D3 _pdut4.bit._D3
#define PDUT4_D4 _pdut4.bit._D4
#define PDUT4_D5 _pdut4.bit._D5
#define PDUT4_D6 _pdut4.bit._D6
#define PDUT4_D7 _pdut4.bit._D7
#define PDUT4_D8 _pdut4.bit._D8
#define PDUT4_D9 _pdut4.bit._D9
#define PDUT4_D10 _pdut4.bit._D10
#define PDUT4_D11 _pdut4.bit._D11
#define PDUT4_D12 _pdut4.bit._D12
#define PDUT4_D13 _pdut4.bit._D13
#define PDUT4_D14 _pdut4.bit._D14
#define PDUT4_D15 _pdut4.bit._D15
#define PDUT4_D _pdut4.bitc._D
__IO_EXTERN __io PCN4STR _pcn4;  
#define PCN4 _pcn4.word
#define PCN4_OSEL _pcn4.bit._OSEL
#define PCN4_OE _pcn4.bit._OE
#define PCN4_IRS0 _pcn4.bit._IRS0
#define PCN4_IRS1 _pcn4.bit._IRS1
#define PCN4_IRQF _pcn4.bit._IRQF
#define PCN4_IREN _pcn4.bit._IREN
#define PCN4_EGS0 _pcn4.bit._EGS0
#define PCN4_EGS1 _pcn4.bit._EGS1
#define PCN4_PGMS _pcn4.bit._PGMS
#define PCN4_CKS0 _pcn4.bit._CKS0
#define PCN4_CKS1 _pcn4.bit._CKS1
#define PCN4_RTRG _pcn4.bit._RTRG
#define PCN4_MDSE _pcn4.bit._MDSE
#define PCN4_STGR _pcn4.bit._STGR
#define PCN4_CNTE _pcn4.bit._CNTE
#define PCN4_IRS _pcn4.bitc._IRS
#define PCN4_EGS _pcn4.bitc._EGS
#define PCN4_CKS _pcn4.bitc._CKS
__IO_EXTERN __io PCNL4STR _pcnl4;  
#define PCNL4 _pcnl4.byte
#define PCNL4_OSEL _pcnl4.bit._OSEL
#define PCNL4_OE _pcnl4.bit._OE
#define PCNL4_IRS0 _pcnl4.bit._IRS0
#define PCNL4_IRS1 _pcnl4.bit._IRS1
#define PCNL4_IRQF _pcnl4.bit._IRQF
#define PCNL4_IREN _pcnl4.bit._IREN
#define PCNL4_EGS0 _pcnl4.bit._EGS0
#define PCNL4_EGS1 _pcnl4.bit._EGS1
#define PCNL4_IRS _pcnl4.bitc._IRS
#define PCNL4_EGS _pcnl4.bitc._EGS
__IO_EXTERN __io PCNH4STR _pcnh4;  
#define PCNH4 _pcnh4.byte
#define PCNH4_PGMS _pcnh4.bit._PGMS
#define PCNH4_CKS0 _pcnh4.bit._CKS0
#define PCNH4_CKS1 _pcnh4.bit._CKS1
#define PCNH4_RTRG _pcnh4.bit._RTRG
#define PCNH4_MDSE _pcnh4.bit._MDSE
#define PCNH4_STGR _pcnh4.bit._STGR
#define PCNH4_CNTE _pcnh4.bit._CNTE
#define PCNH4_CKS _pcnh4.bitc._CKS
__IO_EXTERN __io PTMR5STR _ptmr5;  
#define PTMR5 _ptmr5.word
#define PTMR5_D0 _ptmr5.bit._D0
#define PTMR5_D1 _ptmr5.bit._D1
#define PTMR5_D2 _ptmr5.bit._D2
#define PTMR5_D3 _ptmr5.bit._D3
#define PTMR5_D4 _ptmr5.bit._D4
#define PTMR5_D5 _ptmr5.bit._D5
#define PTMR5_D6 _ptmr5.bit._D6
#define PTMR5_D7 _ptmr5.bit._D7
#define PTMR5_D8 _ptmr5.bit._D8
#define PTMR5_D9 _ptmr5.bit._D9
#define PTMR5_D10 _ptmr5.bit._D10
#define PTMR5_D11 _ptmr5.bit._D11
#define PTMR5_D12 _ptmr5.bit._D12
#define PTMR5_D13 _ptmr5.bit._D13
#define PTMR5_D14 _ptmr5.bit._D14
#define PTMR5_D15 _ptmr5.bit._D15
#define PTMR5_D _ptmr5.bitc._D
__IO_EXTERN __io PCSR5STR _pcsr5;  
#define PCSR5 _pcsr5.word
#define PCSR5_D0 _pcsr5.bit._D0
#define PCSR5_D1 _pcsr5.bit._D1
#define PCSR5_D2 _pcsr5.bit._D2
#define PCSR5_D3 _pcsr5.bit._D3
#define PCSR5_D4 _pcsr5.bit._D4
#define PCSR5_D5 _pcsr5.bit._D5
#define PCSR5_D6 _pcsr5.bit._D6
#define PCSR5_D7 _pcsr5.bit._D7
#define PCSR5_D8 _pcsr5.bit._D8
#define PCSR5_D9 _pcsr5.bit._D9
#define PCSR5_D10 _pcsr5.bit._D10
#define PCSR5_D11 _pcsr5.bit._D11
#define PCSR5_D12 _pcsr5.bit._D12
#define PCSR5_D13 _pcsr5.bit._D13
#define PCSR5_D14 _pcsr5.bit._D14
#define PCSR5_D15 _pcsr5.bit._D15
#define PCSR5_D _pcsr5.bitc._D
__IO_EXTERN __io PDUT5STR _pdut5;  
#define PDUT5 _pdut5.word
#define PDUT5_D0 _pdut5.bit._D0
#define PDUT5_D1 _pdut5.bit._D1
#define PDUT5_D2 _pdut5.bit._D2
#define PDUT5_D3 _pdut5.bit._D3
#define PDUT5_D4 _pdut5.bit._D4
#define PDUT5_D5 _pdut5.bit._D5
#define PDUT5_D6 _pdut5.bit._D6
#define PDUT5_D7 _pdut5.bit._D7
#define PDUT5_D8 _pdut5.bit._D8
#define PDUT5_D9 _pdut5.bit._D9
#define PDUT5_D10 _pdut5.bit._D10
#define PDUT5_D11 _pdut5.bit._D11
#define PDUT5_D12 _pdut5.bit._D12
#define PDUT5_D13 _pdut5.bit._D13
#define PDUT5_D14 _pdut5.bit._D14
#define PDUT5_D15 _pdut5.bit._D15
#define PDUT5_D _pdut5.bitc._D
__IO_EXTERN __io PCN5STR _pcn5;  
#define PCN5 _pcn5.word
#define PCN5_OSEL _pcn5.bit._OSEL
#define PCN5_OE _pcn5.bit._OE
#define PCN5_IRS0 _pcn5.bit._IRS0
#define PCN5_IRS1 _pcn5.bit._IRS1
#define PCN5_IRQF _pcn5.bit._IRQF
#define PCN5_IREN _pcn5.bit._IREN
#define PCN5_EGS0 _pcn5.bit._EGS0
#define PCN5_EGS1 _pcn5.bit._EGS1
#define PCN5_PGMS _pcn5.bit._PGMS
#define PCN5_CKS0 _pcn5.bit._CKS0
#define PCN5_CKS1 _pcn5.bit._CKS1
#define PCN5_RTRG _pcn5.bit._RTRG
#define PCN5_MDSE _pcn5.bit._MDSE
#define PCN5_STGR _pcn5.bit._STGR
#define PCN5_CNTE _pcn5.bit._CNTE
#define PCN5_IRS _pcn5.bitc._IRS
#define PCN5_EGS _pcn5.bitc._EGS
#define PCN5_CKS _pcn5.bitc._CKS
__IO_EXTERN __io PCNL5STR _pcnl5;  
#define PCNL5 _pcnl5.byte
#define PCNL5_OSEL _pcnl5.bit._OSEL
#define PCNL5_OE _pcnl5.bit._OE
#define PCNL5_IRS0 _pcnl5.bit._IRS0
#define PCNL5_IRS1 _pcnl5.bit._IRS1
#define PCNL5_IRQF _pcnl5.bit._IRQF
#define PCNL5_IREN _pcnl5.bit._IREN
#define PCNL5_EGS0 _pcnl5.bit._EGS0
#define PCNL5_EGS1 _pcnl5.bit._EGS1
#define PCNL5_IRS _pcnl5.bitc._IRS
#define PCNL5_EGS _pcnl5.bitc._EGS
__IO_EXTERN __io PCNH5STR _pcnh5;  
#define PCNH5 _pcnh5.byte
#define PCNH5_PGMS _pcnh5.bit._PGMS
#define PCNH5_CKS0 _pcnh5.bit._CKS0
#define PCNH5_CKS1 _pcnh5.bit._CKS1
#define PCNH5_RTRG _pcnh5.bit._RTRG
#define PCNH5_MDSE _pcnh5.bit._MDSE
#define PCNH5_STGR _pcnh5.bit._STGR
#define PCNH5_CNTE _pcnh5.bit._CNTE
#define PCNH5_CKS _pcnh5.bitc._CKS
__IO_EXTERN __io IBSR0STR _ibsr0;  
#define IBSR0 _ibsr0.byte
#define IBSR0_ADT _ibsr0.bit._ADT
#define IBSR0_GCA _ibsr0.bit._GCA
#define IBSR0_AAS _ibsr0.bit._AAS
#define IBSR0_TRX _ibsr0.bit._TRX
#define IBSR0_LRB _ibsr0.bit._LRB
#define IBSR0_AL _ibsr0.bit._AL
#define IBSR0_RSC _ibsr0.bit._RSC
#define IBSR0_BB _ibsr0.bit._BB
__IO_EXTERN __io IBCR0STR _ibcr0;  
#define IBCR0 _ibcr0.byte
#define IBCR0_INT _ibcr0.bit._INT
#define IBCR0_INTE _ibcr0.bit._INTE
#define IBCR0_GCAA _ibcr0.bit._GCAA
#define IBCR0_ACK _ibcr0.bit._ACK
#define IBCR0_MSS _ibcr0.bit._MSS
#define IBCR0_SCC _ibcr0.bit._SCC
#define IBCR0_BEIE _ibcr0.bit._BEIE
#define IBCR0_BER _ibcr0.bit._BER
__IO_EXTERN __io ITBA0STR _itba0;  
#define ITBA0 _itba0.word
#define ITBA0_TA0 _itba0.bit._TA0
#define ITBA0_TA1 _itba0.bit._TA1
#define ITBA0_TA2 _itba0.bit._TA2
#define ITBA0_TA3 _itba0.bit._TA3
#define ITBA0_TA4 _itba0.bit._TA4
#define ITBA0_TA5 _itba0.bit._TA5
#define ITBA0_TA6 _itba0.bit._TA6
#define ITBA0_TA7 _itba0.bit._TA7
#define ITBA0_TA8 _itba0.bit._TA8
#define ITBA0_TA9 _itba0.bit._TA9
#define ITBA0_TA _itba0.bitc._TA
__IO_EXTERN __io ITBAL0STR _itbal0;  
#define ITBAL0 _itbal0.byte
#define ITBAL0_TA0 _itbal0.bit._TA0
#define ITBAL0_TA1 _itbal0.bit._TA1
#define ITBAL0_TA2 _itbal0.bit._TA2
#define ITBAL0_TA3 _itbal0.bit._TA3
#define ITBAL0_TA4 _itbal0.bit._TA4
#define ITBAL0_TA5 _itbal0.bit._TA5
#define ITBAL0_TA6 _itbal0.bit._TA6
#define ITBAL0_TA7 _itbal0.bit._TA7
__IO_EXTERN __io ITBAH0STR _itbah0;  
#define ITBAH0 _itbah0.byte
#define ITBAH0_TA8 _itbah0.bit._TA8
#define ITBAH0_TA9 _itbah0.bit._TA9
__IO_EXTERN __io ITMK0STR _itmk0;  
#define ITMK0 _itmk0.word
#define ITMK0_TM0 _itmk0.bit._TM0
#define ITMK0_TM1 _itmk0.bit._TM1
#define ITMK0_TM2 _itmk0.bit._TM2
#define ITMK0_TM3 _itmk0.bit._TM3
#define ITMK0_TM4 _itmk0.bit._TM4
#define ITMK0_TM5 _itmk0.bit._TM5
#define ITMK0_TM6 _itmk0.bit._TM6
#define ITMK0_TM7 _itmk0.bit._TM7
#define ITMK0_TM8 _itmk0.bit._TM8
#define ITMK0_TM9 _itmk0.bit._TM9
#define ITMK0_RAL _itmk0.bit._RAL
#define ITMK0_ENTB _itmk0.bit._ENTB
#define ITMK0_TM _itmk0.bitc._TM
__IO_EXTERN __io ITMKL0STR _itmkl0;  
#define ITMKL0 _itmkl0.byte
#define ITMKL0_TM0 _itmkl0.bit._TM0
#define ITMKL0_TM1 _itmkl0.bit._TM1
#define ITMKL0_TM2 _itmkl0.bit._TM2
#define ITMKL0_TM3 _itmkl0.bit._TM3
#define ITMKL0_TM4 _itmkl0.bit._TM4
#define ITMKL0_TM5 _itmkl0.bit._TM5
#define ITMKL0_TM6 _itmkl0.bit._TM6
#define ITMKL0_TM7 _itmkl0.bit._TM7
__IO_EXTERN __io ITMKH0STR _itmkh0;  
#define ITMKH0 _itmkh0.byte
#define ITMKH0_TM8 _itmkh0.bit._TM8
#define ITMKH0_TM9 _itmkh0.bit._TM9
#define ITMKH0_RAL _itmkh0.bit._RAL
#define ITMKH0_ENTB _itmkh0.bit._ENTB
__IO_EXTERN __io ISBA0STR _isba0;  
#define ISBA0 _isba0.byte
#define ISBA0_SA0 _isba0.bit._SA0
#define ISBA0_SA1 _isba0.bit._SA1
#define ISBA0_SA2 _isba0.bit._SA2
#define ISBA0_SA3 _isba0.bit._SA3
#define ISBA0_SA4 _isba0.bit._SA4
#define ISBA0_SA5 _isba0.bit._SA5
#define ISBA0_SA6 _isba0.bit._SA6
#define ISBA0_SA _isba0.bitc._SA
__IO_EXTERN __io ISMK0STR _ismk0;  
#define ISMK0 _ismk0.byte
#define ISMK0_SM0 _ismk0.bit._SM0
#define ISMK0_SM1 _ismk0.bit._SM1
#define ISMK0_SM2 _ismk0.bit._SM2
#define ISMK0_SM3 _ismk0.bit._SM3
#define ISMK0_SM4 _ismk0.bit._SM4
#define ISMK0_SM5 _ismk0.bit._SM5
#define ISMK0_SM6 _ismk0.bit._SM6
#define ISMK0_ENSB _ismk0.bit._ENSB
#define ISMK0_SM _ismk0.bitc._SM
__IO_EXTERN __io IDAR0STR _idar0;  
#define IDAR0 _idar0.byte
#define IDAR0_D0 _idar0.bit._D0
#define IDAR0_D1 _idar0.bit._D1
#define IDAR0_D2 _idar0.bit._D2
#define IDAR0_D3 _idar0.bit._D3
#define IDAR0_D4 _idar0.bit._D4
#define IDAR0_D5 _idar0.bit._D5
#define IDAR0_D6 _idar0.bit._D6
#define IDAR0_D7 _idar0.bit._D7
__IO_EXTERN __io ICCR0STR _iccr0;  
#define ICCR0 _iccr0.byte
#define ICCR0_CS0 _iccr0.bit._CS0
#define ICCR0_CS1 _iccr0.bit._CS1
#define ICCR0_CS2 _iccr0.bit._CS2
#define ICCR0_CS3 _iccr0.bit._CS3
#define ICCR0_CS4 _iccr0.bit._CS4
#define ICCR0_EN _iccr0.bit._EN
#define ICCR0_NSF _iccr0.bit._NSF
#define ICCR0_CS _iccr0.bitc._CS
__IO_EXTERN __io IBSR1STR _ibsr1;  
#define IBSR1 _ibsr1.byte
#define IBSR1_ADT _ibsr1.bit._ADT
#define IBSR1_GCA _ibsr1.bit._GCA
#define IBSR1_AAS _ibsr1.bit._AAS
#define IBSR1_TRX _ibsr1.bit._TRX
#define IBSR1_LRB _ibsr1.bit._LRB
#define IBSR1_AL _ibsr1.bit._AL
#define IBSR1_RSC _ibsr1.bit._RSC
#define IBSR1_BB _ibsr1.bit._BB
__IO_EXTERN __io IBCR1STR _ibcr1;  
#define IBCR1 _ibcr1.byte
#define IBCR1_INT _ibcr1.bit._INT
#define IBCR1_INTE _ibcr1.bit._INTE
#define IBCR1_GCAA _ibcr1.bit._GCAA
#define IBCR1_ACK _ibcr1.bit._ACK
#define IBCR1_MSS _ibcr1.bit._MSS
#define IBCR1_SCC _ibcr1.bit._SCC
#define IBCR1_BEIE _ibcr1.bit._BEIE
#define IBCR1_BER _ibcr1.bit._BER
__IO_EXTERN __io ITBA1STR _itba1;  
#define ITBA1 _itba1.word
#define ITBA1_TA0 _itba1.bit._TA0
#define ITBA1_TA1 _itba1.bit._TA1
#define ITBA1_TA2 _itba1.bit._TA2
#define ITBA1_TA3 _itba1.bit._TA3
#define ITBA1_TA4 _itba1.bit._TA4
#define ITBA1_TA5 _itba1.bit._TA5
#define ITBA1_TA6 _itba1.bit._TA6
#define ITBA1_TA7 _itba1.bit._TA7
#define ITBA1_TA8 _itba1.bit._TA8
#define ITBA1_TA9 _itba1.bit._TA9
#define ITBA1_TA _itba1.bitc._TA
__IO_EXTERN __io ITBAL1STR _itbal1;  
#define ITBAL1 _itbal1.byte
#define ITBAL1_TA0 _itbal1.bit._TA0
#define ITBAL1_TA1 _itbal1.bit._TA1
#define ITBAL1_TA2 _itbal1.bit._TA2
#define ITBAL1_TA3 _itbal1.bit._TA3
#define ITBAL1_TA4 _itbal1.bit._TA4
#define ITBAL1_TA5 _itbal1.bit._TA5
#define ITBAL1_TA6 _itbal1.bit._TA6
#define ITBAL1_TA7 _itbal1.bit._TA7
__IO_EXTERN __io ITBAH1STR _itbah1;  
#define ITBAH1 _itbah1.byte
#define ITBAH1_TA8 _itbah1.bit._TA8
#define ITBAH1_TA9 _itbah1.bit._TA9
__IO_EXTERN __io ITMK1STR _itmk1;  
#define ITMK1 _itmk1.word
#define ITMK1_TM0 _itmk1.bit._TM0
#define ITMK1_TM1 _itmk1.bit._TM1
#define ITMK1_TM2 _itmk1.bit._TM2
#define ITMK1_TM3 _itmk1.bit._TM3
#define ITMK1_TM4 _itmk1.bit._TM4
#define ITMK1_TM5 _itmk1.bit._TM5
#define ITMK1_TM6 _itmk1.bit._TM6
#define ITMK1_TM7 _itmk1.bit._TM7
#define ITMK1_TM8 _itmk1.bit._TM8
#define ITMK1_TM9 _itmk1.bit._TM9
#define ITMK1_RAL _itmk1.bit._RAL
#define ITMK1_ENTB _itmk1.bit._ENTB
#define ITMK1_TM _itmk1.bitc._TM
__IO_EXTERN __io ITMKL1STR _itmkl1;  
#define ITMKL1 _itmkl1.byte
#define ITMKL1_TM0 _itmkl1.bit._TM0
#define ITMKL1_TM1 _itmkl1.bit._TM1
#define ITMKL1_TM2 _itmkl1.bit._TM2
#define ITMKL1_TM3 _itmkl1.bit._TM3
#define ITMKL1_TM4 _itmkl1.bit._TM4
#define ITMKL1_TM5 _itmkl1.bit._TM5
#define ITMKL1_TM6 _itmkl1.bit._TM6
#define ITMKL1_TM7 _itmkl1.bit._TM7
__IO_EXTERN __io ITMKH1STR _itmkh1;  
#define ITMKH1 _itmkh1.byte
#define ITMKH1_TM8 _itmkh1.bit._TM8
#define ITMKH1_TM9 _itmkh1.bit._TM9
#define ITMKH1_RAL _itmkh1.bit._RAL
#define ITMKH1_ENTB _itmkh1.bit._ENTB
__IO_EXTERN __io ISBA1STR _isba1;  
#define ISBA1 _isba1.byte
#define ISBA1_SA0 _isba1.bit._SA0
#define ISBA1_SA1 _isba1.bit._SA1
#define ISBA1_SA2 _isba1.bit._SA2
#define ISBA1_SA3 _isba1.bit._SA3
#define ISBA1_SA4 _isba1.bit._SA4
#define ISBA1_SA5 _isba1.bit._SA5
#define ISBA1_SA6 _isba1.bit._SA6
#define ISBA1_SA _isba1.bitc._SA
__IO_EXTERN __io ISMK1STR _ismk1;  
#define ISMK1 _ismk1.byte
#define ISMK1_SM0 _ismk1.bit._SM0
#define ISMK1_SM1 _ismk1.bit._SM1
#define ISMK1_SM2 _ismk1.bit._SM2
#define ISMK1_SM3 _ismk1.bit._SM3
#define ISMK1_SM4 _ismk1.bit._SM4
#define ISMK1_SM5 _ismk1.bit._SM5
#define ISMK1_SM6 _ismk1.bit._SM6
#define ISMK1_ENSB _ismk1.bit._ENSB
#define ISMK1_SM _ismk1.bitc._SM
__IO_EXTERN __io IDAR1STR _idar1;  
#define IDAR1 _idar1.byte
#define IDAR1_D0 _idar1.bit._D0
#define IDAR1_D1 _idar1.bit._D1
#define IDAR1_D2 _idar1.bit._D2
#define IDAR1_D3 _idar1.bit._D3
#define IDAR1_D4 _idar1.bit._D4
#define IDAR1_D5 _idar1.bit._D5
#define IDAR1_D6 _idar1.bit._D6
#define IDAR1_D7 _idar1.bit._D7
__IO_EXTERN __io ICCR1STR _iccr1;  
#define ICCR1 _iccr1.byte
#define ICCR1_CS0 _iccr1.bit._CS0
#define ICCR1_CS1 _iccr1.bit._CS1
#define ICCR1_CS2 _iccr1.bit._CS2
#define ICCR1_CS3 _iccr1.bit._CS3
#define ICCR1_CS4 _iccr1.bit._CS4
#define ICCR1_EN _iccr1.bit._EN
#define ICCR1_NSF _iccr1.bit._NSF
#define ICCR1_CS _iccr1.bitc._CS
__IO_EXTERN __io SMR0STR _smr0;  
#define SMR0 _smr0.byte
#define SMR0_SOE _smr0.bit._SOE
#define SMR0_SCKE _smr0.bit._SCKE
#define SMR0_UPCL _smr0.bit._UPCL
#define SMR0_REST _smr0.bit._REST
#define SMR0_EXT _smr0.bit._EXT
#define SMR0_OTO _smr0.bit._OTO
#define SMR0_MD0 _smr0.bit._MD0
#define SMR0_MD1 _smr0.bit._MD1
#define SMR0_MD _smr0.bitc._MD
__IO_EXTERN __io SCR0STR _scr0;  
#define SCR0 _scr0.byte
#define SCR0_TXE _scr0.bit._TXE
#define SCR0_RXE _scr0.bit._RXE
#define SCR0_CRE _scr0.bit._CRE
#define SCR0_AD _scr0.bit._AD
#define SCR0_CL _scr0.bit._CL
#define SCR0_SBL _scr0.bit._SBL
#define SCR0_P _scr0.bit._P
#define SCR0_PEN _scr0.bit._PEN
__IO_EXTERN __io IO_BYTE _tdr0;
#define TDR0 _tdr0   
__IO_EXTERN __io IO_BYTE _rdr0;
#define RDR0 _rdr0   
__IO_EXTERN __io SSR0STR _ssr0;  
#define SSR0 _ssr0.byte
#define SSR0_TIE _ssr0.bit._TIE
#define SSR0_RIE _ssr0.bit._RIE
#define SSR0_BDS _ssr0.bit._BDS
#define SSR0_TDRE _ssr0.bit._TDRE
#define SSR0_RDRF _ssr0.bit._RDRF
#define SSR0_FRE _ssr0.bit._FRE
#define SSR0_ORE _ssr0.bit._ORE
#define SSR0_PE _ssr0.bit._PE
__IO_EXTERN __io ECCR0STR _eccr0;  
#define ECCR0 _eccr0.byte
#define ECCR0_TBI _eccr0.bit._TBI
#define ECCR0_RBI _eccr0.bit._RBI
#define ECCR0_BIE _eccr0.bit._BIE
#define ECCR0_SSM _eccr0.bit._SSM
#define ECCR0_SCDE _eccr0.bit._SCDE
#define ECCR0_MS _eccr0.bit._MS
#define ECCR0_LBR _eccr0.bit._LBR
#define ECCR0_INV _eccr0.bit._INV
__IO_EXTERN __io ESCR0STR _escr0;  
#define ESCR0 _escr0.byte
#define ESCR0_SCES _escr0.bit._SCES
#define ESCR0_CCO _escr0.bit._CCO
#define ESCR0_SIOP _escr0.bit._SIOP
#define ESCR0_SOPE _escr0.bit._SOPE
#define ESCR0_LBL0 _escr0.bit._LBL0
#define ESCR0_LBL1 _escr0.bit._LBL1
#define ESCR0_LBD _escr0.bit._LBD
#define ESCR0_LBIE _escr0.bit._LBIE
#define ESCR0_LBL _escr0.bitc._LBL
__IO_EXTERN __io BGR0STR _bgr0;  
#define BGR0 _bgr0.word
#define BGR0_BGR0 _bgr0.bit._BGR0
#define BGR0_BGR1 _bgr0.bit._BGR1
#define BGR0_BGR2 _bgr0.bit._BGR2
#define BGR0_BGR3 _bgr0.bit._BGR3
#define BGR0_BGR4 _bgr0.bit._BGR4
#define BGR0_BGR5 _bgr0.bit._BGR5
#define BGR0_BGR6 _bgr0.bit._BGR6
#define BGR0_BGR7 _bgr0.bit._BGR7
#define BGR0_BGR8 _bgr0.bit._BGR8
#define BGR0_BGR9 _bgr0.bit._BGR9
#define BGR0_BGR10 _bgr0.bit._BGR10
#define BGR0_BGR11 _bgr0.bit._BGR11
#define BGR0_BGR12 _bgr0.bit._BGR12
#define BGR0_BGR13 _bgr0.bit._BGR13
#define BGR0_BGR14 _bgr0.bit._BGR14
#define BGR0_BGR15 _bgr0.bit._BGR15
#define BGR0_BGR _bgr0.bitc._BGR
__IO_EXTERN __io BGRL0STR _bgrl0;  
#define BGRL0 _bgrl0.byte
#define BGRL0_BGR0 _bgrl0.bit._BGR0
#define BGRL0_BGR1 _bgrl0.bit._BGR1
#define BGRL0_BGR2 _bgrl0.bit._BGR2
#define BGRL0_BGR3 _bgrl0.bit._BGR3
#define BGRL0_BGR4 _bgrl0.bit._BGR4
#define BGRL0_BGR5 _bgrl0.bit._BGR5
#define BGRL0_BGR6 _bgrl0.bit._BGR6
#define BGRL0_BGR7 _bgrl0.bit._BGR7
__IO_EXTERN __io BGRH0STR _bgrh0;  
#define BGRH0 _bgrh0.byte
#define BGRH0_BGR8 _bgrh0.bit._BGR8
#define BGRH0_BGR9 _bgrh0.bit._BGR9
#define BGRH0_BGR10 _bgrh0.bit._BGR10
#define BGRH0_BGR11 _bgrh0.bit._BGR11
#define BGRH0_BGR12 _bgrh0.bit._BGR12
#define BGRH0_BGR13 _bgrh0.bit._BGR13
#define BGRH0_BGR14 _bgrh0.bit._BGR14
#define BGRH0_BGR15 _bgrh0.bit._BGR15
__IO_EXTERN __io ESIR0STR _esir0;  
#define ESIR0 _esir0.byte
#define ESIR0_AICD _esir0.bit._AICD
#define ESIR0_RBI _esir0.bit._RBI
#define ESIR0_RDRF _esir0.bit._RDRF
#define ESIR0_TDRE _esir0.bit._TDRE
__IO_EXTERN __io SMR1STR _smr1;  
#define SMR1 _smr1.byte
#define SMR1_SOE _smr1.bit._SOE
#define SMR1_SCKE _smr1.bit._SCKE
#define SMR1_UPCL _smr1.bit._UPCL
#define SMR1_REST _smr1.bit._REST
#define SMR1_EXT _smr1.bit._EXT
#define SMR1_OTO _smr1.bit._OTO
#define SMR1_MD0 _smr1.bit._MD0
#define SMR1_MD1 _smr1.bit._MD1
#define SMR1_MD _smr1.bitc._MD
__IO_EXTERN __io SCR1STR _scr1;  
#define SCR1 _scr1.byte
#define SCR1_TXE _scr1.bit._TXE
#define SCR1_RXE _scr1.bit._RXE
#define SCR1_CRE _scr1.bit._CRE
#define SCR1_AD _scr1.bit._AD
#define SCR1_CL _scr1.bit._CL
#define SCR1_SBL _scr1.bit._SBL
#define SCR1_P _scr1.bit._P
#define SCR1_PEN _scr1.bit._PEN
__IO_EXTERN __io IO_BYTE _tdr1;
#define TDR1 _tdr1   
__IO_EXTERN __io IO_BYTE _rdr1;
#define RDR1 _rdr1   
__IO_EXTERN __io SSR1STR _ssr1;  
#define SSR1 _ssr1.byte
#define SSR1_TIE _ssr1.bit._TIE
#define SSR1_RIE _ssr1.bit._RIE
#define SSR1_BDS _ssr1.bit._BDS
#define SSR1_TDRE _ssr1.bit._TDRE
#define SSR1_RDRF _ssr1.bit._RDRF
#define SSR1_FRE _ssr1.bit._FRE
#define SSR1_ORE _ssr1.bit._ORE
#define SSR1_PE _ssr1.bit._PE
__IO_EXTERN __io ECCR1STR _eccr1;  
#define ECCR1 _eccr1.byte
#define ECCR1_TBI _eccr1.bit._TBI
#define ECCR1_RBI _eccr1.bit._RBI
#define ECCR1_BIE _eccr1.bit._BIE
#define ECCR1_SSM _eccr1.bit._SSM
#define ECCR1_SCDE _eccr1.bit._SCDE
#define ECCR1_MS _eccr1.bit._MS
#define ECCR1_LBR _eccr1.bit._LBR
#define ECCR1_INV _eccr1.bit._INV
__IO_EXTERN __io ESCR1STR _escr1;  
#define ESCR1 _escr1.byte
#define ESCR1_SCES _escr1.bit._SCES
#define ESCR1_CCO _escr1.bit._CCO
#define ESCR1_SIOP _escr1.bit._SIOP
#define ESCR1_SOPE _escr1.bit._SOPE
#define ESCR1_LBL0 _escr1.bit._LBL0
#define ESCR1_LBL1 _escr1.bit._LBL1
#define ESCR1_LBD _escr1.bit._LBD
#define ESCR1_LBIE _escr1.bit._LBIE
#define ESCR1_LBL _escr1.bitc._LBL
__IO_EXTERN __io BGR1STR _bgr1;  
#define BGR1 _bgr1.word
#define BGR1_BGR0 _bgr1.bit._BGR0
#define BGR1_BGR1 _bgr1.bit._BGR1
#define BGR1_BGR2 _bgr1.bit._BGR2
#define BGR1_BGR3 _bgr1.bit._BGR3
#define BGR1_BGR4 _bgr1.bit._BGR4
#define BGR1_BGR5 _bgr1.bit._BGR5
#define BGR1_BGR6 _bgr1.bit._BGR6
#define BGR1_BGR7 _bgr1.bit._BGR7
#define BGR1_BGR8 _bgr1.bit._BGR8
#define BGR1_BGR9 _bgr1.bit._BGR9
#define BGR1_BGR10 _bgr1.bit._BGR10
#define BGR1_BGR11 _bgr1.bit._BGR11
#define BGR1_BGR12 _bgr1.bit._BGR12
#define BGR1_BGR13 _bgr1.bit._BGR13
#define BGR1_BGR14 _bgr1.bit._BGR14
#define BGR1_BGR15 _bgr1.bit._BGR15
#define BGR1_BGR _bgr1.bitc._BGR
__IO_EXTERN __io BGRL1STR _bgrl1;  
#define BGRL1 _bgrl1.byte
#define BGRL1_BGR0 _bgrl1.bit._BGR0
#define BGRL1_BGR1 _bgrl1.bit._BGR1
#define BGRL1_BGR2 _bgrl1.bit._BGR2
#define BGRL1_BGR3 _bgrl1.bit._BGR3
#define BGRL1_BGR4 _bgrl1.bit._BGR4
#define BGRL1_BGR5 _bgrl1.bit._BGR5
#define BGRL1_BGR6 _bgrl1.bit._BGR6
#define BGRL1_BGR7 _bgrl1.bit._BGR7
__IO_EXTERN __io BGRH1STR _bgrh1;  
#define BGRH1 _bgrh1.byte
#define BGRH1_BGR8 _bgrh1.bit._BGR8
#define BGRH1_BGR9 _bgrh1.bit._BGR9
#define BGRH1_BGR10 _bgrh1.bit._BGR10
#define BGRH1_BGR11 _bgrh1.bit._BGR11
#define BGRH1_BGR12 _bgrh1.bit._BGR12
#define BGRH1_BGR13 _bgrh1.bit._BGR13
#define BGRH1_BGR14 _bgrh1.bit._BGR14
#define BGRH1_BGR15 _bgrh1.bit._BGR15
__IO_EXTERN __io ESIR1STR _esir1;  
#define ESIR1 _esir1.byte
#define ESIR1_AICD _esir1.bit._AICD
#define ESIR1_RBI _esir1.bit._RBI
#define ESIR1_RDRF _esir1.bit._RDRF
#define ESIR1_TDRE _esir1.bit._TDRE
__IO_EXTERN __io SMR2STR _smr2;  
#define SMR2 _smr2.byte
#define SMR2_SOE _smr2.bit._SOE
#define SMR2_SCKE _smr2.bit._SCKE
#define SMR2_UPCL _smr2.bit._UPCL
#define SMR2_REST _smr2.bit._REST
#define SMR2_EXT _smr2.bit._EXT
#define SMR2_OTO _smr2.bit._OTO
#define SMR2_MD0 _smr2.bit._MD0
#define SMR2_MD1 _smr2.bit._MD1
#define SMR2_MD _smr2.bitc._MD
__IO_EXTERN __io SCR2STR _scr2;  
#define SCR2 _scr2.byte
#define SCR2_TXE _scr2.bit._TXE
#define SCR2_RXE _scr2.bit._RXE
#define SCR2_CRE _scr2.bit._CRE
#define SCR2_AD _scr2.bit._AD
#define SCR2_CL _scr2.bit._CL
#define SCR2_SBL _scr2.bit._SBL
#define SCR2_P _scr2.bit._P
#define SCR2_PEN _scr2.bit._PEN
__IO_EXTERN __io IO_BYTE _tdr2;
#define TDR2 _tdr2   
__IO_EXTERN __io IO_BYTE _rdr2;
#define RDR2 _rdr2   
__IO_EXTERN __io SSR2STR _ssr2;  
#define SSR2 _ssr2.byte
#define SSR2_TIE _ssr2.bit._TIE
#define SSR2_RIE _ssr2.bit._RIE
#define SSR2_BDS _ssr2.bit._BDS
#define SSR2_TDRE _ssr2.bit._TDRE
#define SSR2_RDRF _ssr2.bit._RDRF
#define SSR2_FRE _ssr2.bit._FRE
#define SSR2_ORE _ssr2.bit._ORE
#define SSR2_PE _ssr2.bit._PE
__IO_EXTERN __io ECCR2STR _eccr2;  
#define ECCR2 _eccr2.byte
#define ECCR2_TBI _eccr2.bit._TBI
#define ECCR2_RBI _eccr2.bit._RBI
#define ECCR2_BIE _eccr2.bit._BIE
#define ECCR2_SSM _eccr2.bit._SSM
#define ECCR2_SCDE _eccr2.bit._SCDE
#define ECCR2_MS _eccr2.bit._MS
#define ECCR2_LBR _eccr2.bit._LBR
#define ECCR2_INV _eccr2.bit._INV
__IO_EXTERN __io ESCR2STR _escr2;  
#define ESCR2 _escr2.byte
#define ESCR2_SCES _escr2.bit._SCES
#define ESCR2_CCO _escr2.bit._CCO
#define ESCR2_SIOP _escr2.bit._SIOP
#define ESCR2_SOPE _escr2.bit._SOPE
#define ESCR2_LBL0 _escr2.bit._LBL0
#define ESCR2_LBL1 _escr2.bit._LBL1
#define ESCR2_LBD _escr2.bit._LBD
#define ESCR2_LBIE _escr2.bit._LBIE
#define ESCR2_LBL _escr2.bitc._LBL
__IO_EXTERN __io BGR2STR _bgr2;  
#define BGR2 _bgr2.word
#define BGR2_BGR0 _bgr2.bit._BGR0
#define BGR2_BGR1 _bgr2.bit._BGR1
#define BGR2_BGR2 _bgr2.bit._BGR2
#define BGR2_BGR3 _bgr2.bit._BGR3
#define BGR2_BGR4 _bgr2.bit._BGR4
#define BGR2_BGR5 _bgr2.bit._BGR5
#define BGR2_BGR6 _bgr2.bit._BGR6
#define BGR2_BGR7 _bgr2.bit._BGR7
#define BGR2_BGR8 _bgr2.bit._BGR8
#define BGR2_BGR9 _bgr2.bit._BGR9
#define BGR2_BGR10 _bgr2.bit._BGR10
#define BGR2_BGR11 _bgr2.bit._BGR11
#define BGR2_BGR12 _bgr2.bit._BGR12
#define BGR2_BGR13 _bgr2.bit._BGR13
#define BGR2_BGR14 _bgr2.bit._BGR14
#define BGR2_BGR15 _bgr2.bit._BGR15
#define BGR2_BGR _bgr2.bitc._BGR
__IO_EXTERN __io BGRL2STR _bgrl2;  
#define BGRL2 _bgrl2.byte
#define BGRL2_BGR0 _bgrl2.bit._BGR0
#define BGRL2_BGR1 _bgrl2.bit._BGR1
#define BGRL2_BGR2 _bgrl2.bit._BGR2
#define BGRL2_BGR3 _bgrl2.bit._BGR3
#define BGRL2_BGR4 _bgrl2.bit._BGR4
#define BGRL2_BGR5 _bgrl2.bit._BGR5
#define BGRL2_BGR6 _bgrl2.bit._BGR6
#define BGRL2_BGR7 _bgrl2.bit._BGR7
__IO_EXTERN __io BGRH2STR _bgrh2;  
#define BGRH2 _bgrh2.byte
#define BGRH2_BGR8 _bgrh2.bit._BGR8
#define BGRH2_BGR9 _bgrh2.bit._BGR9
#define BGRH2_BGR10 _bgrh2.bit._BGR10
#define BGRH2_BGR11 _bgrh2.bit._BGR11
#define BGRH2_BGR12 _bgrh2.bit._BGR12
#define BGRH2_BGR13 _bgrh2.bit._BGR13
#define BGRH2_BGR14 _bgrh2.bit._BGR14
#define BGRH2_BGR15 _bgrh2.bit._BGR15
__IO_EXTERN __io ESIR2STR _esir2;  
#define ESIR2 _esir2.byte
#define ESIR2_AICD _esir2.bit._AICD
#define ESIR2_RBI _esir2.bit._RBI
#define ESIR2_RDRF _esir2.bit._RDRF
#define ESIR2_TDRE _esir2.bit._TDRE
__IO_EXTERN __io SMR3STR _smr3;  
#define SMR3 _smr3.byte
#define SMR3_SOE _smr3.bit._SOE
#define SMR3_SCKE _smr3.bit._SCKE
#define SMR3_UPCL _smr3.bit._UPCL
#define SMR3_REST _smr3.bit._REST
#define SMR3_EXT _smr3.bit._EXT
#define SMR3_OTO _smr3.bit._OTO
#define SMR3_MD0 _smr3.bit._MD0
#define SMR3_MD1 _smr3.bit._MD1
#define SMR3_MD _smr3.bitc._MD
__IO_EXTERN __io SCR3STR _scr3;  
#define SCR3 _scr3.byte
#define SCR3_TXE _scr3.bit._TXE
#define SCR3_RXE _scr3.bit._RXE
#define SCR3_CRE _scr3.bit._CRE
#define SCR3_AD _scr3.bit._AD
#define SCR3_CL _scr3.bit._CL
#define SCR3_SBL _scr3.bit._SBL
#define SCR3_P _scr3.bit._P
#define SCR3_PEN _scr3.bit._PEN
__IO_EXTERN __io IO_BYTE _tdr3;
#define TDR3 _tdr3   
__IO_EXTERN __io IO_BYTE _rdr3;
#define RDR3 _rdr3   
__IO_EXTERN __io SSR3STR _ssr3;  
#define SSR3 _ssr3.byte
#define SSR3_TIE _ssr3.bit._TIE
#define SSR3_RIE _ssr3.bit._RIE
#define SSR3_BDS _ssr3.bit._BDS
#define SSR3_TDRE _ssr3.bit._TDRE
#define SSR3_RDRF _ssr3.bit._RDRF
#define SSR3_FRE _ssr3.bit._FRE
#define SSR3_ORE _ssr3.bit._ORE
#define SSR3_PE _ssr3.bit._PE
__IO_EXTERN __io ECCR3STR _eccr3;  
#define ECCR3 _eccr3.byte
#define ECCR3_TBI _eccr3.bit._TBI
#define ECCR3_RBI _eccr3.bit._RBI
#define ECCR3_BIE _eccr3.bit._BIE
#define ECCR3_SSM _eccr3.bit._SSM
#define ECCR3_SCDE _eccr3.bit._SCDE
#define ECCR3_MS _eccr3.bit._MS
#define ECCR3_LBR _eccr3.bit._LBR
#define ECCR3_INV _eccr3.bit._INV
__IO_EXTERN __io ESCR3STR _escr3;  
#define ESCR3 _escr3.byte
#define ESCR3_SCES _escr3.bit._SCES
#define ESCR3_CCO _escr3.bit._CCO
#define ESCR3_SIOP _escr3.bit._SIOP
#define ESCR3_SOPE _escr3.bit._SOPE
#define ESCR3_LBL0 _escr3.bit._LBL0
#define ESCR3_LBL1 _escr3.bit._LBL1
#define ESCR3_LBD _escr3.bit._LBD
#define ESCR3_LBIE _escr3.bit._LBIE
#define ESCR3_LBL _escr3.bitc._LBL
__IO_EXTERN __io BGR3STR _bgr3;  
#define BGR3 _bgr3.word
#define BGR3_BGR0 _bgr3.bit._BGR0
#define BGR3_BGR1 _bgr3.bit._BGR1
#define BGR3_BGR2 _bgr3.bit._BGR2
#define BGR3_BGR3 _bgr3.bit._BGR3
#define BGR3_BGR4 _bgr3.bit._BGR4
#define BGR3_BGR5 _bgr3.bit._BGR5
#define BGR3_BGR6 _bgr3.bit._BGR6
#define BGR3_BGR7 _bgr3.bit._BGR7
#define BGR3_BGR8 _bgr3.bit._BGR8
#define BGR3_BGR9 _bgr3.bit._BGR9
#define BGR3_BGR10 _bgr3.bit._BGR10
#define BGR3_BGR11 _bgr3.bit._BGR11
#define BGR3_BGR12 _bgr3.bit._BGR12
#define BGR3_BGR13 _bgr3.bit._BGR13
#define BGR3_BGR14 _bgr3.bit._BGR14
#define BGR3_BGR15 _bgr3.bit._BGR15
#define BGR3_BGR _bgr3.bitc._BGR
__IO_EXTERN __io BGRL3STR _bgrl3;  
#define BGRL3 _bgrl3.byte
#define BGRL3_BGR0 _bgrl3.bit._BGR0
#define BGRL3_BGR1 _bgrl3.bit._BGR1
#define BGRL3_BGR2 _bgrl3.bit._BGR2
#define BGRL3_BGR3 _bgrl3.bit._BGR3
#define BGRL3_BGR4 _bgrl3.bit._BGR4
#define BGRL3_BGR5 _bgrl3.bit._BGR5
#define BGRL3_BGR6 _bgrl3.bit._BGR6
#define BGRL3_BGR7 _bgrl3.bit._BGR7
__IO_EXTERN __io BGRH3STR _bgrh3;  
#define BGRH3 _bgrh3.byte
#define BGRH3_BGR8 _bgrh3.bit._BGR8
#define BGRH3_BGR9 _bgrh3.bit._BGR9
#define BGRH3_BGR10 _bgrh3.bit._BGR10
#define BGRH3_BGR11 _bgrh3.bit._BGR11
#define BGRH3_BGR12 _bgrh3.bit._BGR12
#define BGRH3_BGR13 _bgrh3.bit._BGR13
#define BGRH3_BGR14 _bgrh3.bit._BGR14
#define BGRH3_BGR15 _bgrh3.bit._BGR15
__IO_EXTERN __io ESIR3STR _esir3;  
#define ESIR3 _esir3.byte
#define ESIR3_AICD _esir3.bit._AICD
#define ESIR3_RBI _esir3.bit._RBI
#define ESIR3_RDRF _esir3.bit._RDRF
#define ESIR3_TDRE _esir3.bit._TDRE
__IO_EXTENDED IO_BYTE _bapl0;
#define BAPL0 _bapl0   
__IO_EXTENDED IO_BYTE _bapm0;
#define BAPM0 _bapm0   
__IO_EXTENDED IO_BYTE _baph0;
#define BAPH0 _baph0   
__IO_EXTENDED DMACS0STR _dmacs0;  
#define DMACS0 _dmacs0.byte
#define DMACS0_SE _dmacs0.bit._SE
#define DMACS0_DIR _dmacs0.bit._DIR
#define DMACS0_BF _dmacs0.bit._BF
#define DMACS0_BW _dmacs0.bit._BW
#define DMACS0_IF _dmacs0.bit._IF
#define DMACS0_BPD _dmacs0.bit._BPD
__IO_EXTENDED IO_WORD _ioa0;
#define IOA0 _ioa0   
__IO_EXTENDED IO_BYTE _ioal0;
#define IOAL0 _ioal0   
__IO_EXTENDED IO_BYTE _ioah0;
#define IOAH0 _ioah0   
__IO_EXTENDED IO_WORD _dct0;
#define DCT0 _dct0   
__IO_EXTENDED IO_BYTE _dctl0;
#define DCTL0 _dctl0   
__IO_EXTENDED IO_BYTE _dcth0;
#define DCTH0 _dcth0   
__IO_EXTENDED IO_BYTE _bapl1;
#define BAPL1 _bapl1   
__IO_EXTENDED IO_BYTE _bapm1;
#define BAPM1 _bapm1   
__IO_EXTENDED IO_BYTE _baph1;
#define BAPH1 _baph1   
__IO_EXTENDED DMACS1STR _dmacs1;  
#define DMACS1 _dmacs1.byte
#define DMACS1_SE _dmacs1.bit._SE
#define DMACS1_DIR _dmacs1.bit._DIR
#define DMACS1_BF _dmacs1.bit._BF
#define DMACS1_BW _dmacs1.bit._BW
#define DMACS1_IF _dmacs1.bit._IF
#define DMACS1_BPD _dmacs1.bit._BPD
__IO_EXTENDED IO_WORD _ioa1;
#define IOA1 _ioa1   
__IO_EXTENDED IO_BYTE _ioal1;
#define IOAL1 _ioal1   
__IO_EXTENDED IO_BYTE _ioah1;
#define IOAH1 _ioah1   
__IO_EXTENDED IO_WORD _dct1;
#define DCT1 _dct1   
__IO_EXTENDED IO_BYTE _dctl1;
#define DCTL1 _dctl1   
__IO_EXTENDED IO_BYTE _dcth1;
#define DCTH1 _dcth1   
__IO_EXTENDED IO_BYTE _bapl2;
#define BAPL2 _bapl2   
__IO_EXTENDED IO_BYTE _bapm2;
#define BAPM2 _bapm2   
__IO_EXTENDED IO_BYTE _baph2;
#define BAPH2 _baph2   
__IO_EXTENDED DMACS2STR _dmacs2;  
#define DMACS2 _dmacs2.byte
#define DMACS2_SE _dmacs2.bit._SE
#define DMACS2_DIR _dmacs2.bit._DIR
#define DMACS2_BF _dmacs2.bit._BF
#define DMACS2_BW _dmacs2.bit._BW
#define DMACS2_IF _dmacs2.bit._IF
#define DMACS2_BPD _dmacs2.bit._BPD
__IO_EXTENDED IO_WORD _ioa2;
#define IOA2 _ioa2   
__IO_EXTENDED IO_BYTE _ioal2;
#define IOAL2 _ioal2   
__IO_EXTENDED IO_BYTE _ioah2;
#define IOAH2 _ioah2   
__IO_EXTENDED IO_WORD _dct2;
#define DCT2 _dct2   
__IO_EXTENDED IO_BYTE _dctl2;
#define DCTL2 _dctl2   
__IO_EXTENDED IO_BYTE _dcth2;
#define DCTH2 _dcth2   
__IO_EXTENDED IO_BYTE _bapl3;
#define BAPL3 _bapl3   
__IO_EXTENDED IO_BYTE _bapm3;
#define BAPM3 _bapm3   
__IO_EXTENDED IO_BYTE _baph3;
#define BAPH3 _baph3   
__IO_EXTENDED DMACS3STR _dmacs3;  
#define DMACS3 _dmacs3.byte
#define DMACS3_SE _dmacs3.bit._SE
#define DMACS3_DIR _dmacs3.bit._DIR
#define DMACS3_BF _dmacs3.bit._BF
#define DMACS3_BW _dmacs3.bit._BW
#define DMACS3_IF _dmacs3.bit._IF
#define DMACS3_BPD _dmacs3.bit._BPD
__IO_EXTENDED IO_WORD _ioa3;
#define IOA3 _ioa3   
__IO_EXTENDED IO_BYTE _ioal3;
#define IOAL3 _ioal3   
__IO_EXTENDED IO_BYTE _ioah3;
#define IOAH3 _ioah3   
__IO_EXTENDED IO_WORD _dct3;
#define DCT3 _dct3   
__IO_EXTENDED IO_BYTE _dctl3;
#define DCTL3 _dctl3   
__IO_EXTENDED IO_BYTE _dcth3;
#define DCTH3 _dcth3   
__IO_EXTENDED IO_BYTE _bapl4;
#define BAPL4 _bapl4   
__IO_EXTENDED IO_BYTE _bapm4;
#define BAPM4 _bapm4   
__IO_EXTENDED IO_BYTE _baph4;
#define BAPH4 _baph4   
__IO_EXTENDED DMACS4STR _dmacs4;  
#define DMACS4 _dmacs4.byte
#define DMACS4_SE _dmacs4.bit._SE
#define DMACS4_DIR _dmacs4.bit._DIR
#define DMACS4_BF _dmacs4.bit._BF
#define DMACS4_BW _dmacs4.bit._BW
#define DMACS4_IF _dmacs4.bit._IF
#define DMACS4_BPD _dmacs4.bit._BPD
__IO_EXTENDED IO_WORD _ioa4;
#define IOA4 _ioa4   
__IO_EXTENDED IO_BYTE _ioal4;
#define IOAL4 _ioal4   
__IO_EXTENDED IO_BYTE _ioah4;
#define IOAH4 _ioah4   
__IO_EXTENDED IO_WORD _dct4;
#define DCT4 _dct4   
__IO_EXTENDED IO_BYTE _dctl4;
#define DCTL4 _dctl4   
__IO_EXTENDED IO_BYTE _dcth4;
#define DCTH4 _dcth4   
__IO_EXTENDED IO_BYTE _bapl5;
#define BAPL5 _bapl5   
__IO_EXTENDED IO_BYTE _bapm5;
#define BAPM5 _bapm5   
__IO_EXTENDED IO_BYTE _baph5;
#define BAPH5 _baph5   
__IO_EXTENDED DMACS5STR _dmacs5;  
#define DMACS5 _dmacs5.byte
#define DMACS5_SE _dmacs5.bit._SE
#define DMACS5_DIR _dmacs5.bit._DIR
#define DMACS5_BF _dmacs5.bit._BF
#define DMACS5_BW _dmacs5.bit._BW
#define DMACS5_IF _dmacs5.bit._IF
#define DMACS5_BPD _dmacs5.bit._BPD
__IO_EXTENDED IO_WORD _ioa5;
#define IOA5 _ioa5   
__IO_EXTENDED IO_BYTE _ioal5;
#define IOAL5 _ioal5   
__IO_EXTENDED IO_BYTE _ioah5;
#define IOAH5 _ioah5   
__IO_EXTENDED IO_WORD _dct5;
#define DCT5 _dct5   
__IO_EXTENDED IO_BYTE _dctl5;
#define DCTL5 _dctl5   
__IO_EXTENDED IO_BYTE _dcth5;
#define DCTH5 _dcth5   
__IO_EXTENDED IO_BYTE _disel0;
#define DISEL0 _disel0   
__IO_EXTENDED IO_BYTE _disel1;
#define DISEL1 _disel1   
__IO_EXTENDED IO_BYTE _disel2;
#define DISEL2 _disel2   
__IO_EXTENDED IO_BYTE _disel3;
#define DISEL3 _disel3   
__IO_EXTENDED IO_BYTE _disel4;
#define DISEL4 _disel4   
__IO_EXTENDED IO_BYTE _disel5;
#define DISEL5 _disel5   
__IO_EXTENDED DSRSTR _dsr;  
#define DSR _dsr.word
#define DSR_DTE0 _dsr.bit._DTE0
#define DSR_DTE1 _dsr.bit._DTE1
#define DSR_DTE2 _dsr.bit._DTE2
#define DSR_DTE3 _dsr.bit._DTE3
#define DSR_DTE4 _dsr.bit._DTE4
#define DSR_DTE5 _dsr.bit._DTE5
__IO_EXTENDED DSRLSTR _dsrl;  
#define DSRL _dsrl.byte
#define DSRL_DTE0 _dsrl.bit._DTE0
#define DSRL_DTE1 _dsrl.bit._DTE1
#define DSRL_DTE2 _dsrl.bit._DTE2
#define DSRL_DTE3 _dsrl.bit._DTE3
#define DSRL_DTE4 _dsrl.bit._DTE4
#define DSRL_DTE5 _dsrl.bit._DTE5
__IO_EXTENDED IO_BYTE _dsrh;
#define DSRH _dsrh   
__IO_EXTENDED DSSRSTR _dssr;  
#define DSSR _dssr.word
#define DSSR_STP0 _dssr.bit._STP0
#define DSSR_STP1 _dssr.bit._STP1
#define DSSR_STP2 _dssr.bit._STP2
#define DSSR_STP3 _dssr.bit._STP3
#define DSSR_STP4 _dssr.bit._STP4
#define DSSR_STP5 _dssr.bit._STP5
__IO_EXTENDED DSSRLSTR _dssrl;  
#define DSSRL _dssrl.byte
#define DSSRL_STP0 _dssrl.bit._STP0
#define DSSRL_STP1 _dssrl.bit._STP1
#define DSSRL_STP2 _dssrl.bit._STP2
#define DSSRL_STP3 _dssrl.bit._STP3
#define DSSRL_STP4 _dssrl.bit._STP4
#define DSSRL_STP5 _dssrl.bit._STP5
__IO_EXTENDED IO_BYTE _dssrh;
#define DSSRH _dssrh   
__IO_EXTENDED DERSTR _der;  
#define DER _der.word
#define DER_EN0 _der.bit._EN0
#define DER_EN1 _der.bit._EN1
#define DER_EN2 _der.bit._EN2
#define DER_EN3 _der.bit._EN3
#define DER_EN4 _der.bit._EN4
#define DER_EN5 _der.bit._EN5
__IO_EXTENDED DERLSTR _derl;  
#define DERL _derl.byte
#define DERL_EN0 _derl.bit._EN0
#define DERL_EN1 _derl.bit._EN1
#define DERL_EN2 _derl.bit._EN2
#define DERL_EN3 _derl.bit._EN3
#define DERL_EN4 _derl.bit._EN4
#define DERL_EN5 _derl.bit._EN5
__IO_EXTENDED IO_BYTE _derh;
#define DERH _derh   
__IO_EXTENDED ICRSTR _icr;  
#define ICR _icr.word
#define ICR_IL0 _icr.bit._IL0
#define ICR_IL1 _icr.bit._IL1
#define ICR_IL2 _icr.bit._IL2
#define ICR_IX0 _icr.bit._IX0
#define ICR_IX1 _icr.bit._IX1
#define ICR_IX2 _icr.bit._IX2
#define ICR_IX3 _icr.bit._IX3
#define ICR_IX4 _icr.bit._IX4
#define ICR_IX5 _icr.bit._IX5
#define ICR_IX6 _icr.bit._IX6
#define ICR_IX7 _icr.bit._IX7
#define ICR_IL _icr.bitc._IL
#define ICR_IX _icr.bitc._IX
__IO_EXTENDED ILRSTR _ilr;  
#define ILR _ilr.byte
#define ILR_IL0 _ilr.bit._IL0
#define ILR_IL1 _ilr.bit._IL1
#define ILR_IL2 _ilr.bit._IL2
#define ILR_IL _ilr.bitc._IL
__IO_EXTENDED IDXSTR _idx;  
#define IDX _idx.byte
#define IDX_IX0 _idx.bit._IX0
#define IDX_IX1 _idx.bit._IX1
#define IDX_IX2 _idx.bit._IX2
#define IDX_IX3 _idx.bit._IX3
#define IDX_IX4 _idx.bit._IX4
#define IDX_IX5 _idx.bit._IX5
#define IDX_IX6 _idx.bit._IX6
#define IDX_IX7 _idx.bit._IX7
#define IDX_IX _idx.bitc._IX
__IO_EXTENDED TBRSTR _tbr;  
#define TBR _tbr.word
#define TBR_TB10 _tbr.bit._TB10
#define TBR_TB11 _tbr.bit._TB11
#define TBR_TB12 _tbr.bit._TB12
#define TBR_TB13 _tbr.bit._TB13
#define TBR_TB14 _tbr.bit._TB14
#define TBR_TB15 _tbr.bit._TB15
#define TBR_TB16 _tbr.bit._TB16
#define TBR_TB17 _tbr.bit._TB17
#define TBR_TB18 _tbr.bit._TB18
#define TBR_TB19 _tbr.bit._TB19
#define TBR_TB20 _tbr.bit._TB20
#define TBR_TB21 _tbr.bit._TB21
#define TBR_TB22 _tbr.bit._TB22
#define TBR_TB23 _tbr.bit._TB23
__IO_EXTENDED TBRLSTR _tbrl;  
#define TBRL _tbrl.byte
#define TBRL_TB10 _tbrl.bit._TB10
#define TBRL_TB11 _tbrl.bit._TB11
#define TBRL_TB12 _tbrl.bit._TB12
#define TBRL_TB13 _tbrl.bit._TB13
#define TBRL_TB14 _tbrl.bit._TB14
#define TBRL_TB15 _tbrl.bit._TB15
__IO_EXTENDED TBRHSTR _tbrh;  
#define TBRH _tbrh.byte
#define TBRH_TB16 _tbrh.bit._TB16
#define TBRH_TB17 _tbrh.bit._TB17
#define TBRH_TB18 _tbrh.bit._TB18
#define TBRH_TB19 _tbrh.bit._TB19
#define TBRH_TB20 _tbrh.bit._TB20
#define TBRH_TB21 _tbrh.bit._TB21
#define TBRH_TB22 _tbrh.bit._TB22
#define TBRH_TB23 _tbrh.bit._TB23
__IO_EXTENDED DIRRSTR _dirr;  
#define DIRR _dirr.byte
#define DIRR_R0 _dirr.bit._R0
__IO_EXTENDED NMISTR _nmi;  
#define NMI _nmi.byte
#define NMI_FLAG _nmi.bit._FLAG
#define NMI_EN _nmi.bit._EN
#define NMI_LEV _nmi.bit._LEV
#define NMI_INT9FIX _nmi.bit._INT9FIX
__IO_EXTENDED EDSU2STR _edsu2;  
#define EDSU2 _edsu2.word
#define EDSU2_RSEL0 _edsu2.bit._RSEL0
#define EDSU2_RSEL1 _edsu2.bit._RSEL1
#define EDSU2_RSEL2 _edsu2.bit._RSEL2
#define EDSU2_RSEL3 _edsu2.bit._RSEL3
#define EDSU2_RSEL4 _edsu2.bit._RSEL4
#define EDSU2_RSEL5 _edsu2.bit._RSEL5
#define EDSU2_RSEL6 _edsu2.bit._RSEL6
#define EDSU2_RSEL7 _edsu2.bit._RSEL7
#define EDSU2_TSEL0 _edsu2.bit._TSEL0
#define EDSU2_TSEL1 _edsu2.bit._TSEL1
#define EDSU2_TSEL2 _edsu2.bit._TSEL2
#define EDSU2_TSEL3 _edsu2.bit._TSEL3
#define EDSU2_TSEL4 _edsu2.bit._TSEL4
#define EDSU2_TSEL5 _edsu2.bit._TSEL5
#define EDSU2_TSEL6 _edsu2.bit._TSEL6
#define EDSU2_TSEL7 _edsu2.bit._TSEL7
#define EDSU2_RSEL _edsu2.bitc._RSEL
#define EDSU2_TSEL _edsu2.bitc._TSEL
__IO_EXTENDED ROMMSTR _romm;  
#define ROMM _romm.byte
#define ROMM_MI _romm.bit._MI
#define ROMM_SZ0 _romm.bit._SZ0
#define ROMM_SZ1 _romm.bit._SZ1
#define ROMM_BS0 _romm.bit._BS0
#define ROMM_BS1 _romm.bit._BS1
#define ROMM_BS2 _romm.bit._BS2
#define ROMM_BS3 _romm.bit._BS3
__IO_EXTENDED EDSUSTR _edsu;  
#define EDSU _edsu.byte
#define EDSU_RINT _edsu.bit._RINT
#define EDSU_RIE _edsu.bit._RIE
#define EDSU_SEL0 _edsu.bit._SEL0
#define EDSU_SEL1 _edsu.bit._SEL1
#define EDSU_TINT _edsu.bit._TINT
#define EDSU_TIE _edsu.bit._TIE
#define EDSU_EN _edsu.bit._EN
#define EDSU_SEL _edsu.bitc._SEL
__IO_EXTENDED PFCS0STR _pfcs0;  
#define PFCS0 _pfcs0.word
#define PFCS0_I0 _pfcs0.bit._I0
#define PFCS0_I1 _pfcs0.bit._I1
#define PFCS0_IE0 _pfcs0.bit._IE0
#define PFCS0_IE1 _pfcs0.bit._IE1
#define PFCS0_PE0 _pfcs0.bit._PE0
#define PFCS0_PE1 _pfcs0.bit._PE1
#define PFCS0_AR _pfcs0.bit._AR
#define PFCS0_AM _pfcs0.bit._AM
#define PFCS0_DMA _pfcs0.bit._DMA
#define PFCS0_CPU _pfcs0.bit._CPU
#define PFCS0_DATA _pfcs0.bit._DATA
#define PFCS0_CODE _pfcs0.bit._CODE
#define PFCS0_WORD _pfcs0.bit._WORD
#define PFCS0_BYTE _pfcs0.bit._BYTE
#define PFCS0_WRITE _pfcs0.bit._WRITE
#define PFCS0_READ _pfcs0.bit._READ
__IO_EXTENDED PFCS1STR _pfcs1;  
#define PFCS1 _pfcs1.word
#define PFCS1_I0 _pfcs1.bit._I0
#define PFCS1_I1 _pfcs1.bit._I1
#define PFCS1_IE0 _pfcs1.bit._IE0
#define PFCS1_IE1 _pfcs1.bit._IE1
#define PFCS1_PE0 _pfcs1.bit._PE0
#define PFCS1_PE1 _pfcs1.bit._PE1
#define PFCS1_AR _pfcs1.bit._AR
#define PFCS1_AM _pfcs1.bit._AM
#define PFCS1_DMA _pfcs1.bit._DMA
#define PFCS1_CPU _pfcs1.bit._CPU
#define PFCS1_DATA _pfcs1.bit._DATA
#define PFCS1_CODE _pfcs1.bit._CODE
#define PFCS1_WORD _pfcs1.bit._WORD
#define PFCS1_BYTE _pfcs1.bit._BYTE
#define PFCS1_WRITE _pfcs1.bit._WRITE
#define PFCS1_READ _pfcs1.bit._READ
__IO_EXTENDED PFCS2STR _pfcs2;  
#define PFCS2 _pfcs2.word
#define PFCS2_I0 _pfcs2.bit._I0
#define PFCS2_I1 _pfcs2.bit._I1
#define PFCS2_IE0 _pfcs2.bit._IE0
#define PFCS2_IE1 _pfcs2.bit._IE1
#define PFCS2_PE0 _pfcs2.bit._PE0
#define PFCS2_PE1 _pfcs2.bit._PE1
#define PFCS2_AR _pfcs2.bit._AR
#define PFCS2_AM _pfcs2.bit._AM
#define PFCS2_DMA _pfcs2.bit._DMA
#define PFCS2_CPU _pfcs2.bit._CPU
#define PFCS2_DATA _pfcs2.bit._DATA
#define PFCS2_CODE _pfcs2.bit._CODE
#define PFCS2_WORD _pfcs2.bit._WORD
#define PFCS2_BYTE _pfcs2.bit._BYTE
#define PFCS2_WRITE _pfcs2.bit._WRITE
#define PFCS2_READ _pfcs2.bit._READ
__IO_EXTENDED PFCS3STR _pfcs3;  
#define PFCS3 _pfcs3.word
#define PFCS3_I0 _pfcs3.bit._I0
#define PFCS3_I1 _pfcs3.bit._I1
#define PFCS3_IE0 _pfcs3.bit._IE0
#define PFCS3_IE1 _pfcs3.bit._IE1
#define PFCS3_PE0 _pfcs3.bit._PE0
#define PFCS3_PE1 _pfcs3.bit._PE1
#define PFCS3_AR _pfcs3.bit._AR
#define PFCS3_AM _pfcs3.bit._AM
#define PFCS3_DMA _pfcs3.bit._DMA
#define PFCS3_CPU _pfcs3.bit._CPU
#define PFCS3_DATA _pfcs3.bit._DATA
#define PFCS3_CODE _pfcs3.bit._CODE
#define PFCS3_WORD _pfcs3.bit._WORD
#define PFCS3_BYTE _pfcs3.bit._BYTE
#define PFCS3_WRITE _pfcs3.bit._WRITE
#define PFCS3_READ _pfcs3.bit._READ
__IO_EXTENDED PFAL0STR _pfal0;  
#define PFAL0 _pfal0.byte
#define PFAL0_PFA0 _pfal0.bit._PFA0
#define PFAL0_PFA1 _pfal0.bit._PFA1
#define PFAL0_PFA2 _pfal0.bit._PFA2
#define PFAL0_PFA3 _pfal0.bit._PFA3
#define PFAL0_PFA4 _pfal0.bit._PFA4
#define PFAL0_PFA5 _pfal0.bit._PFA5
#define PFAL0_PFA6 _pfal0.bit._PFA6
#define PFAL0_PFA7 _pfal0.bit._PFA7
__IO_EXTENDED PFAM0STR _pfam0;  
#define PFAM0 _pfam0.byte
#define PFAM0_PFA8 _pfam0.bit._PFA8
#define PFAM0_PFA9 _pfam0.bit._PFA9
#define PFAM0_PFA10 _pfam0.bit._PFA10
#define PFAM0_PFA11 _pfam0.bit._PFA11
#define PFAM0_PFA12 _pfam0.bit._PFA12
#define PFAM0_PFA13 _pfam0.bit._PFA13
#define PFAM0_PFA14 _pfam0.bit._PFA14
#define PFAM0_PFA15 _pfam0.bit._PFA15
__IO_EXTENDED PFAH0STR _pfah0;  
#define PFAH0 _pfah0.byte
#define PFAH0_PFA16 _pfah0.bit._PFA16
#define PFAH0_PFA17 _pfah0.bit._PFA17
#define PFAH0_PFA18 _pfah0.bit._PFA18
#define PFAH0_PFA19 _pfah0.bit._PFA19
#define PFAH0_PFA20 _pfah0.bit._PFA20
#define PFAH0_PFA21 _pfah0.bit._PFA21
#define PFAH0_PFA22 _pfah0.bit._PFA22
#define PFAH0_PFA23 _pfah0.bit._PFA23
__IO_EXTENDED PFAL1STR _pfal1;  
#define PFAL1 _pfal1.byte
#define PFAL1_PFA0 _pfal1.bit._PFA0
#define PFAL1_PFA1 _pfal1.bit._PFA1
#define PFAL1_PFA2 _pfal1.bit._PFA2
#define PFAL1_PFA3 _pfal1.bit._PFA3
#define PFAL1_PFA4 _pfal1.bit._PFA4
#define PFAL1_PFA5 _pfal1.bit._PFA5
#define PFAL1_PFA6 _pfal1.bit._PFA6
#define PFAL1_PFA7 _pfal1.bit._PFA7
__IO_EXTENDED PFAM1STR _pfam1;  
#define PFAM1 _pfam1.byte
#define PFAM1_PFA8 _pfam1.bit._PFA8
#define PFAM1_PFA9 _pfam1.bit._PFA9
#define PFAM1_PFA10 _pfam1.bit._PFA10
#define PFAM1_PFA11 _pfam1.bit._PFA11
#define PFAM1_PFA12 _pfam1.bit._PFA12
#define PFAM1_PFA13 _pfam1.bit._PFA13
#define PFAM1_PFA14 _pfam1.bit._PFA14
#define PFAM1_PFA15 _pfam1.bit._PFA15
__IO_EXTENDED PFAH1STR _pfah1;  
#define PFAH1 _pfah1.byte
#define PFAH1_PFA16 _pfah1.bit._PFA16
#define PFAH1_PFA17 _pfah1.bit._PFA17
#define PFAH1_PFA18 _pfah1.bit._PFA18
#define PFAH1_PFA19 _pfah1.bit._PFA19
#define PFAH1_PFA20 _pfah1.bit._PFA20
#define PFAH1_PFA21 _pfah1.bit._PFA21
#define PFAH1_PFA22 _pfah1.bit._PFA22
#define PFAH1_PFA23 _pfah1.bit._PFA23
__IO_EXTENDED PFAL2STR _pfal2;  
#define PFAL2 _pfal2.byte
#define PFAL2_PFA0 _pfal2.bit._PFA0
#define PFAL2_PFA1 _pfal2.bit._PFA1
#define PFAL2_PFA2 _pfal2.bit._PFA2
#define PFAL2_PFA3 _pfal2.bit._PFA3
#define PFAL2_PFA4 _pfal2.bit._PFA4
#define PFAL2_PFA5 _pfal2.bit._PFA5
#define PFAL2_PFA6 _pfal2.bit._PFA6
#define PFAL2_PFA7 _pfal2.bit._PFA7
__IO_EXTENDED PFAM2STR _pfam2;  
#define PFAM2 _pfam2.byte
#define PFAM2_PFA8 _pfam2.bit._PFA8
#define PFAM2_PFA9 _pfam2.bit._PFA9
#define PFAM2_PFA10 _pfam2.bit._PFA10
#define PFAM2_PFA11 _pfam2.bit._PFA11
#define PFAM2_PFA12 _pfam2.bit._PFA12
#define PFAM2_PFA13 _pfam2.bit._PFA13
#define PFAM2_PFA14 _pfam2.bit._PFA14
#define PFAM2_PFA15 _pfam2.bit._PFA15
__IO_EXTENDED PFAH2STR _pfah2;  
#define PFAH2 _pfah2.byte
#define PFAH2_PFA16 _pfah2.bit._PFA16
#define PFAH2_PFA17 _pfah2.bit._PFA17
#define PFAH2_PFA18 _pfah2.bit._PFA18
#define PFAH2_PFA19 _pfah2.bit._PFA19
#define PFAH2_PFA20 _pfah2.bit._PFA20
#define PFAH2_PFA21 _pfah2.bit._PFA21
#define PFAH2_PFA22 _pfah2.bit._PFA22
#define PFAH2_PFA23 _pfah2.bit._PFA23
__IO_EXTENDED PFAL3STR _pfal3;  
#define PFAL3 _pfal3.byte
#define PFAL3_PFA0 _pfal3.bit._PFA0
#define PFAL3_PFA1 _pfal3.bit._PFA1
#define PFAL3_PFA2 _pfal3.bit._PFA2
#define PFAL3_PFA3 _pfal3.bit._PFA3
#define PFAL3_PFA4 _pfal3.bit._PFA4
#define PFAL3_PFA5 _pfal3.bit._PFA5
#define PFAL3_PFA6 _pfal3.bit._PFA6
#define PFAL3_PFA7 _pfal3.bit._PFA7
__IO_EXTENDED PFAM3STR _pfam3;  
#define PFAM3 _pfam3.byte
#define PFAM3_PFA8 _pfam3.bit._PFA8
#define PFAM3_PFA9 _pfam3.bit._PFA9
#define PFAM3_PFA10 _pfam3.bit._PFA10
#define PFAM3_PFA11 _pfam3.bit._PFA11
#define PFAM3_PFA12 _pfam3.bit._PFA12
#define PFAM3_PFA13 _pfam3.bit._PFA13
#define PFAM3_PFA14 _pfam3.bit._PFA14
#define PFAM3_PFA15 _pfam3.bit._PFA15
__IO_EXTENDED PFAH3STR _pfah3;  
#define PFAH3 _pfah3.byte
#define PFAH3_PFA16 _pfah3.bit._PFA16
#define PFAH3_PFA17 _pfah3.bit._PFA17
#define PFAH3_PFA18 _pfah3.bit._PFA18
#define PFAH3_PFA19 _pfah3.bit._PFA19
#define PFAH3_PFA20 _pfah3.bit._PFA20
#define PFAH3_PFA21 _pfah3.bit._PFA21
#define PFAH3_PFA22 _pfah3.bit._PFA22
#define PFAH3_PFA23 _pfah3.bit._PFA23
__IO_EXTENDED PFAL4STR _pfal4;  
#define PFAL4 _pfal4.byte
#define PFAL4_PFA0 _pfal4.bit._PFA0
#define PFAL4_PFA1 _pfal4.bit._PFA1
#define PFAL4_PFA2 _pfal4.bit._PFA2
#define PFAL4_PFA3 _pfal4.bit._PFA3
#define PFAL4_PFA4 _pfal4.bit._PFA4
#define PFAL4_PFA5 _pfal4.bit._PFA5
#define PFAL4_PFA6 _pfal4.bit._PFA6
#define PFAL4_PFA7 _pfal4.bit._PFA7
__IO_EXTENDED PFAM4STR _pfam4;  
#define PFAM4 _pfam4.byte
#define PFAM4_PFA8 _pfam4.bit._PFA8
#define PFAM4_PFA9 _pfam4.bit._PFA9
#define PFAM4_PFA10 _pfam4.bit._PFA10
#define PFAM4_PFA11 _pfam4.bit._PFA11
#define PFAM4_PFA12 _pfam4.bit._PFA12
#define PFAM4_PFA13 _pfam4.bit._PFA13
#define PFAM4_PFA14 _pfam4.bit._PFA14
#define PFAM4_PFA15 _pfam4.bit._PFA15
__IO_EXTENDED PFAH4STR _pfah4;  
#define PFAH4 _pfah4.byte
#define PFAH4_PFA16 _pfah4.bit._PFA16
#define PFAH4_PFA17 _pfah4.bit._PFA17
#define PFAH4_PFA18 _pfah4.bit._PFA18
#define PFAH4_PFA19 _pfah4.bit._PFA19
#define PFAH4_PFA20 _pfah4.bit._PFA20
#define PFAH4_PFA21 _pfah4.bit._PFA21
#define PFAH4_PFA22 _pfah4.bit._PFA22
#define PFAH4_PFA23 _pfah4.bit._PFA23
__IO_EXTENDED PFAL5STR _pfal5;  
#define PFAL5 _pfal5.byte
#define PFAL5_PFA0 _pfal5.bit._PFA0
#define PFAL5_PFA1 _pfal5.bit._PFA1
#define PFAL5_PFA2 _pfal5.bit._PFA2
#define PFAL5_PFA3 _pfal5.bit._PFA3
#define PFAL5_PFA4 _pfal5.bit._PFA4
#define PFAL5_PFA5 _pfal5.bit._PFA5
#define PFAL5_PFA6 _pfal5.bit._PFA6
#define PFAL5_PFA7 _pfal5.bit._PFA7
__IO_EXTENDED PFAM5STR _pfam5;  
#define PFAM5 _pfam5.byte
#define PFAM5_PFA8 _pfam5.bit._PFA8
#define PFAM5_PFA9 _pfam5.bit._PFA9
#define PFAM5_PFA10 _pfam5.bit._PFA10
#define PFAM5_PFA11 _pfam5.bit._PFA11
#define PFAM5_PFA12 _pfam5.bit._PFA12
#define PFAM5_PFA13 _pfam5.bit._PFA13
#define PFAM5_PFA14 _pfam5.bit._PFA14
#define PFAM5_PFA15 _pfam5.bit._PFA15
__IO_EXTENDED PFAH5STR _pfah5;  
#define PFAH5 _pfah5.byte
#define PFAH5_PFA16 _pfah5.bit._PFA16
#define PFAH5_PFA17 _pfah5.bit._PFA17
#define PFAH5_PFA18 _pfah5.bit._PFA18
#define PFAH5_PFA19 _pfah5.bit._PFA19
#define PFAH5_PFA20 _pfah5.bit._PFA20
#define PFAH5_PFA21 _pfah5.bit._PFA21
#define PFAH5_PFA22 _pfah5.bit._PFA22
#define PFAH5_PFA23 _pfah5.bit._PFA23
__IO_EXTENDED PFAL6STR _pfal6;  
#define PFAL6 _pfal6.byte
#define PFAL6_PFA0 _pfal6.bit._PFA0
#define PFAL6_PFA1 _pfal6.bit._PFA1
#define PFAL6_PFA2 _pfal6.bit._PFA2
#define PFAL6_PFA3 _pfal6.bit._PFA3
#define PFAL6_PFA4 _pfal6.bit._PFA4
#define PFAL6_PFA5 _pfal6.bit._PFA5
#define PFAL6_PFA6 _pfal6.bit._PFA6
#define PFAL6_PFA7 _pfal6.bit._PFA7
__IO_EXTENDED PFAM6STR _pfam6;  
#define PFAM6 _pfam6.byte
#define PFAM6_PFA8 _pfam6.bit._PFA8
#define PFAM6_PFA9 _pfam6.bit._PFA9
#define PFAM6_PFA10 _pfam6.bit._PFA10
#define PFAM6_PFA11 _pfam6.bit._PFA11
#define PFAM6_PFA12 _pfam6.bit._PFA12
#define PFAM6_PFA13 _pfam6.bit._PFA13
#define PFAM6_PFA14 _pfam6.bit._PFA14
#define PFAM6_PFA15 _pfam6.bit._PFA15
__IO_EXTENDED PFAH6STR _pfah6;  
#define PFAH6 _pfah6.byte
#define PFAH6_PFA16 _pfah6.bit._PFA16
#define PFAH6_PFA17 _pfah6.bit._PFA17
#define PFAH6_PFA18 _pfah6.bit._PFA18
#define PFAH6_PFA19 _pfah6.bit._PFA19
#define PFAH6_PFA20 _pfah6.bit._PFA20
#define PFAH6_PFA21 _pfah6.bit._PFA21
#define PFAH6_PFA22 _pfah6.bit._PFA22
#define PFAH6_PFA23 _pfah6.bit._PFA23
__IO_EXTENDED PFAL7STR _pfal7;  
#define PFAL7 _pfal7.byte
#define PFAL7_PFA0 _pfal7.bit._PFA0
#define PFAL7_PFA1 _pfal7.bit._PFA1
#define PFAL7_PFA2 _pfal7.bit._PFA2
#define PFAL7_PFA3 _pfal7.bit._PFA3
#define PFAL7_PFA4 _pfal7.bit._PFA4
#define PFAL7_PFA5 _pfal7.bit._PFA5
#define PFAL7_PFA6 _pfal7.bit._PFA6
#define PFAL7_PFA7 _pfal7.bit._PFA7
__IO_EXTENDED PFAM7STR _pfam7;  
#define PFAM7 _pfam7.byte
#define PFAM7_PFA8 _pfam7.bit._PFA8
#define PFAM7_PFA9 _pfam7.bit._PFA9
#define PFAM7_PFA10 _pfam7.bit._PFA10
#define PFAM7_PFA11 _pfam7.bit._PFA11
#define PFAM7_PFA12 _pfam7.bit._PFA12
#define PFAM7_PFA13 _pfam7.bit._PFA13
#define PFAM7_PFA14 _pfam7.bit._PFA14
#define PFAM7_PFA15 _pfam7.bit._PFA15
__IO_EXTENDED PFAH7STR _pfah7;  
#define PFAH7 _pfah7.byte
#define PFAH7_PFA16 _pfah7.bit._PFA16
#define PFAH7_PFA17 _pfah7.bit._PFA17
#define PFAH7_PFA18 _pfah7.bit._PFA18
#define PFAH7_PFA19 _pfah7.bit._PFA19
#define PFAH7_PFA20 _pfah7.bit._PFA20
#define PFAH7_PFA21 _pfah7.bit._PFA21
#define PFAH7_PFA22 _pfah7.bit._PFA22
#define PFAH7_PFA23 _pfah7.bit._PFA23
__IO_EXTENDED PFD0STR _pfd0;  
#define PFD0 _pfd0.word
#define PFD0_PFD0 _pfd0.bit._PFD0
#define PFD0_PFD1 _pfd0.bit._PFD1
#define PFD0_PFD2 _pfd0.bit._PFD2
#define PFD0_PFD3 _pfd0.bit._PFD3
#define PFD0_PFD4 _pfd0.bit._PFD4
#define PFD0_PFD5 _pfd0.bit._PFD5
#define PFD0_PFD6 _pfd0.bit._PFD6
#define PFD0_PFD7 _pfd0.bit._PFD7
#define PFD0_PFD8 _pfd0.bit._PFD8
#define PFD0_PFD9 _pfd0.bit._PFD9
#define PFD0_PFD10 _pfd0.bit._PFD10
#define PFD0_PFD11 _pfd0.bit._PFD11
#define PFD0_PFD12 _pfd0.bit._PFD12
#define PFD0_PFD13 _pfd0.bit._PFD13
#define PFD0_PFD14 _pfd0.bit._PFD14
#define PFD0_PFD15 _pfd0.bit._PFD15
#define PFD0_PFD _pfd0.bitc._PFD
__IO_EXTENDED PFDL0STR _pfdl0;  
#define PFDL0 _pfdl0.byte
#define PFDL0_PFD0 _pfdl0.bit._PFD0
#define PFDL0_PFD1 _pfdl0.bit._PFD1
#define PFDL0_PFD2 _pfdl0.bit._PFD2
#define PFDL0_PFD3 _pfdl0.bit._PFD3
#define PFDL0_PFD4 _pfdl0.bit._PFD4
#define PFDL0_PFD5 _pfdl0.bit._PFD5
#define PFDL0_PFD6 _pfdl0.bit._PFD6
#define PFDL0_PFD7 _pfdl0.bit._PFD7
__IO_EXTENDED PFDH0STR _pfdh0;  
#define PFDH0 _pfdh0.byte
#define PFDH0_PFD8 _pfdh0.bit._PFD8
#define PFDH0_PFD9 _pfdh0.bit._PFD9
#define PFDH0_PFD10 _pfdh0.bit._PFD10
#define PFDH0_PFD11 _pfdh0.bit._PFD11
#define PFDH0_PFD12 _pfdh0.bit._PFD12
#define PFDH0_PFD13 _pfdh0.bit._PFD13
#define PFDH0_PFD14 _pfdh0.bit._PFD14
#define PFDH0_PFD15 _pfdh0.bit._PFD15
__IO_EXTENDED PFD1STR _pfd1;  
#define PFD1 _pfd1.word
#define PFD1_PFD0 _pfd1.bit._PFD0
#define PFD1_PFD1 _pfd1.bit._PFD1
#define PFD1_PFD2 _pfd1.bit._PFD2
#define PFD1_PFD3 _pfd1.bit._PFD3
#define PFD1_PFD4 _pfd1.bit._PFD4
#define PFD1_PFD5 _pfd1.bit._PFD5
#define PFD1_PFD6 _pfd1.bit._PFD6
#define PFD1_PFD7 _pfd1.bit._PFD7
#define PFD1_PFD8 _pfd1.bit._PFD8
#define PFD1_PFD9 _pfd1.bit._PFD9
#define PFD1_PFD10 _pfd1.bit._PFD10
#define PFD1_PFD11 _pfd1.bit._PFD11
#define PFD1_PFD12 _pfd1.bit._PFD12
#define PFD1_PFD13 _pfd1.bit._PFD13
#define PFD1_PFD14 _pfd1.bit._PFD14
#define PFD1_PFD15 _pfd1.bit._PFD15
#define PFD1_PFD _pfd1.bitc._PFD
__IO_EXTENDED PFDL1STR _pfdl1;  
#define PFDL1 _pfdl1.byte
#define PFDL1_PFD0 _pfdl1.bit._PFD0
#define PFDL1_PFD1 _pfdl1.bit._PFD1
#define PFDL1_PFD2 _pfdl1.bit._PFD2
#define PFDL1_PFD3 _pfdl1.bit._PFD3
#define PFDL1_PFD4 _pfdl1.bit._PFD4
#define PFDL1_PFD5 _pfdl1.bit._PFD5
#define PFDL1_PFD6 _pfdl1.bit._PFD6
#define PFDL1_PFD7 _pfdl1.bit._PFD7
__IO_EXTENDED PFDH1STR _pfdh1;  
#define PFDH1 _pfdh1.byte
#define PFDH1_PFD8 _pfdh1.bit._PFD8
#define PFDH1_PFD9 _pfdh1.bit._PFD9
#define PFDH1_PFD10 _pfdh1.bit._PFD10
#define PFDH1_PFD11 _pfdh1.bit._PFD11
#define PFDH1_PFD12 _pfdh1.bit._PFD12
#define PFDH1_PFD13 _pfdh1.bit._PFD13
#define PFDH1_PFD14 _pfdh1.bit._PFD14
#define PFDH1_PFD15 _pfdh1.bit._PFD15
__IO_EXTENDED PFD2STR _pfd2;  
#define PFD2 _pfd2.word
#define PFD2_PFD0 _pfd2.bit._PFD0
#define PFD2_PFD1 _pfd2.bit._PFD1
#define PFD2_PFD2 _pfd2.bit._PFD2
#define PFD2_PFD3 _pfd2.bit._PFD3
#define PFD2_PFD4 _pfd2.bit._PFD4
#define PFD2_PFD5 _pfd2.bit._PFD5
#define PFD2_PFD6 _pfd2.bit._PFD6
#define PFD2_PFD7 _pfd2.bit._PFD7
#define PFD2_PFD8 _pfd2.bit._PFD8
#define PFD2_PFD9 _pfd2.bit._PFD9
#define PFD2_PFD10 _pfd2.bit._PFD10
#define PFD2_PFD11 _pfd2.bit._PFD11
#define PFD2_PFD12 _pfd2.bit._PFD12
#define PFD2_PFD13 _pfd2.bit._PFD13
#define PFD2_PFD14 _pfd2.bit._PFD14
#define PFD2_PFD15 _pfd2.bit._PFD15
#define PFD2_PFD _pfd2.bitc._PFD
__IO_EXTENDED PFDL2STR _pfdl2;  
#define PFDL2 _pfdl2.byte
#define PFDL2_PFD0 _pfdl2.bit._PFD0
#define PFDL2_PFD1 _pfdl2.bit._PFD1
#define PFDL2_PFD2 _pfdl2.bit._PFD2
#define PFDL2_PFD3 _pfdl2.bit._PFD3
#define PFDL2_PFD4 _pfdl2.bit._PFD4
#define PFDL2_PFD5 _pfdl2.bit._PFD5
#define PFDL2_PFD6 _pfdl2.bit._PFD6
#define PFDL2_PFD7 _pfdl2.bit._PFD7
__IO_EXTENDED PFDH2STR _pfdh2;  
#define PFDH2 _pfdh2.byte
#define PFDH2_PFD8 _pfdh2.bit._PFD8
#define PFDH2_PFD9 _pfdh2.bit._PFD9
#define PFDH2_PFD10 _pfdh2.bit._PFD10
#define PFDH2_PFD11 _pfdh2.bit._PFD11
#define PFDH2_PFD12 _pfdh2.bit._PFD12
#define PFDH2_PFD13 _pfdh2.bit._PFD13
#define PFDH2_PFD14 _pfdh2.bit._PFD14
#define PFDH2_PFD15 _pfdh2.bit._PFD15
__IO_EXTENDED PFD3STR _pfd3;  
#define PFD3 _pfd3.word
#define PFD3_PFD0 _pfd3.bit._PFD0
#define PFD3_PFD1 _pfd3.bit._PFD1
#define PFD3_PFD2 _pfd3.bit._PFD2
#define PFD3_PFD3 _pfd3.bit._PFD3
#define PFD3_PFD4 _pfd3.bit._PFD4
#define PFD3_PFD5 _pfd3.bit._PFD5
#define PFD3_PFD6 _pfd3.bit._PFD6
#define PFD3_PFD7 _pfd3.bit._PFD7
#define PFD3_PFD8 _pfd3.bit._PFD8
#define PFD3_PFD9 _pfd3.bit._PFD9
#define PFD3_PFD10 _pfd3.bit._PFD10
#define PFD3_PFD11 _pfd3.bit._PFD11
#define PFD3_PFD12 _pfd3.bit._PFD12
#define PFD3_PFD13 _pfd3.bit._PFD13
#define PFD3_PFD14 _pfd3.bit._PFD14
#define PFD3_PFD15 _pfd3.bit._PFD15
#define PFD3_PFD _pfd3.bitc._PFD
__IO_EXTENDED PFDL3STR _pfdl3;  
#define PFDL3 _pfdl3.byte
#define PFDL3_PFD0 _pfdl3.bit._PFD0
#define PFDL3_PFD1 _pfdl3.bit._PFD1
#define PFDL3_PFD2 _pfdl3.bit._PFD2
#define PFDL3_PFD3 _pfdl3.bit._PFD3
#define PFDL3_PFD4 _pfdl3.bit._PFD4
#define PFDL3_PFD5 _pfdl3.bit._PFD5
#define PFDL3_PFD6 _pfdl3.bit._PFD6
#define PFDL3_PFD7 _pfdl3.bit._PFD7
__IO_EXTENDED PFDH3STR _pfdh3;  
#define PFDH3 _pfdh3.byte
#define PFDH3_PFD8 _pfdh3.bit._PFD8
#define PFDH3_PFD9 _pfdh3.bit._PFD9
#define PFDH3_PFD10 _pfdh3.bit._PFD10
#define PFDH3_PFD11 _pfdh3.bit._PFD11
#define PFDH3_PFD12 _pfdh3.bit._PFD12
#define PFDH3_PFD13 _pfdh3.bit._PFD13
#define PFDH3_PFD14 _pfdh3.bit._PFD14
#define PFDH3_PFD15 _pfdh3.bit._PFD15
__IO_EXTENDED PFD4STR _pfd4;  
#define PFD4 _pfd4.word
#define PFD4_PFD0 _pfd4.bit._PFD0
#define PFD4_PFD1 _pfd4.bit._PFD1
#define PFD4_PFD2 _pfd4.bit._PFD2
#define PFD4_PFD3 _pfd4.bit._PFD3
#define PFD4_PFD4 _pfd4.bit._PFD4
#define PFD4_PFD5 _pfd4.bit._PFD5
#define PFD4_PFD6 _pfd4.bit._PFD6
#define PFD4_PFD7 _pfd4.bit._PFD7
#define PFD4_PFD8 _pfd4.bit._PFD8
#define PFD4_PFD9 _pfd4.bit._PFD9
#define PFD4_PFD10 _pfd4.bit._PFD10
#define PFD4_PFD11 _pfd4.bit._PFD11
#define PFD4_PFD12 _pfd4.bit._PFD12
#define PFD4_PFD13 _pfd4.bit._PFD13
#define PFD4_PFD14 _pfd4.bit._PFD14
#define PFD4_PFD15 _pfd4.bit._PFD15
#define PFD4_PFD _pfd4.bitc._PFD
__IO_EXTENDED PFDL4STR _pfdl4;  
#define PFDL4 _pfdl4.byte
#define PFDL4_PFD0 _pfdl4.bit._PFD0
#define PFDL4_PFD1 _pfdl4.bit._PFD1
#define PFDL4_PFD2 _pfdl4.bit._PFD2
#define PFDL4_PFD3 _pfdl4.bit._PFD3
#define PFDL4_PFD4 _pfdl4.bit._PFD4
#define PFDL4_PFD5 _pfdl4.bit._PFD5
#define PFDL4_PFD6 _pfdl4.bit._PFD6
#define PFDL4_PFD7 _pfdl4.bit._PFD7
__IO_EXTENDED PFDH4STR _pfdh4;  
#define PFDH4 _pfdh4.byte
#define PFDH4_PFD8 _pfdh4.bit._PFD8
#define PFDH4_PFD9 _pfdh4.bit._PFD9
#define PFDH4_PFD10 _pfdh4.bit._PFD10
#define PFDH4_PFD11 _pfdh4.bit._PFD11
#define PFDH4_PFD12 _pfdh4.bit._PFD12
#define PFDH4_PFD13 _pfdh4.bit._PFD13
#define PFDH4_PFD14 _pfdh4.bit._PFD14
#define PFDH4_PFD15 _pfdh4.bit._PFD15
__IO_EXTENDED PFD5STR _pfd5;  
#define PFD5 _pfd5.word
#define PFD5_PFD0 _pfd5.bit._PFD0
#define PFD5_PFD1 _pfd5.bit._PFD1
#define PFD5_PFD2 _pfd5.bit._PFD2
#define PFD5_PFD3 _pfd5.bit._PFD3
#define PFD5_PFD4 _pfd5.bit._PFD4
#define PFD5_PFD5 _pfd5.bit._PFD5
#define PFD5_PFD6 _pfd5.bit._PFD6
#define PFD5_PFD7 _pfd5.bit._PFD7
#define PFD5_PFD8 _pfd5.bit._PFD8
#define PFD5_PFD9 _pfd5.bit._PFD9
#define PFD5_PFD10 _pfd5.bit._PFD10
#define PFD5_PFD11 _pfd5.bit._PFD11
#define PFD5_PFD12 _pfd5.bit._PFD12
#define PFD5_PFD13 _pfd5.bit._PFD13
#define PFD5_PFD14 _pfd5.bit._PFD14
#define PFD5_PFD15 _pfd5.bit._PFD15
#define PFD5_PFD _pfd5.bitc._PFD
__IO_EXTENDED PFDL5STR _pfdl5;  
#define PFDL5 _pfdl5.byte
#define PFDL5_PFD0 _pfdl5.bit._PFD0
#define PFDL5_PFD1 _pfdl5.bit._PFD1
#define PFDL5_PFD2 _pfdl5.bit._PFD2
#define PFDL5_PFD3 _pfdl5.bit._PFD3
#define PFDL5_PFD4 _pfdl5.bit._PFD4
#define PFDL5_PFD5 _pfdl5.bit._PFD5
#define PFDL5_PFD6 _pfdl5.bit._PFD6
#define PFDL5_PFD7 _pfdl5.bit._PFD7
__IO_EXTENDED PFDH5STR _pfdh5;  
#define PFDH5 _pfdh5.byte
#define PFDH5_PFD8 _pfdh5.bit._PFD8
#define PFDH5_PFD9 _pfdh5.bit._PFD9
#define PFDH5_PFD10 _pfdh5.bit._PFD10
#define PFDH5_PFD11 _pfdh5.bit._PFD11
#define PFDH5_PFD12 _pfdh5.bit._PFD12
#define PFDH5_PFD13 _pfdh5.bit._PFD13
#define PFDH5_PFD14 _pfdh5.bit._PFD14
#define PFDH5_PFD15 _pfdh5.bit._PFD15
__IO_EXTENDED PFD6STR _pfd6;  
#define PFD6 _pfd6.word
#define PFD6_PFD0 _pfd6.bit._PFD0
#define PFD6_PFD1 _pfd6.bit._PFD1
#define PFD6_PFD2 _pfd6.bit._PFD2
#define PFD6_PFD3 _pfd6.bit._PFD3
#define PFD6_PFD4 _pfd6.bit._PFD4
#define PFD6_PFD5 _pfd6.bit._PFD5
#define PFD6_PFD6 _pfd6.bit._PFD6
#define PFD6_PFD7 _pfd6.bit._PFD7
#define PFD6_PFD8 _pfd6.bit._PFD8
#define PFD6_PFD9 _pfd6.bit._PFD9
#define PFD6_PFD10 _pfd6.bit._PFD10
#define PFD6_PFD11 _pfd6.bit._PFD11
#define PFD6_PFD12 _pfd6.bit._PFD12
#define PFD6_PFD13 _pfd6.bit._PFD13
#define PFD6_PFD14 _pfd6.bit._PFD14
#define PFD6_PFD15 _pfd6.bit._PFD15
#define PFD6_PFD _pfd6.bitc._PFD
__IO_EXTENDED PFDL6STR _pfdl6;  
#define PFDL6 _pfdl6.byte
#define PFDL6_PFD0 _pfdl6.bit._PFD0
#define PFDL6_PFD1 _pfdl6.bit._PFD1
#define PFDL6_PFD2 _pfdl6.bit._PFD2
#define PFDL6_PFD3 _pfdl6.bit._PFD3
#define PFDL6_PFD4 _pfdl6.bit._PFD4
#define PFDL6_PFD5 _pfdl6.bit._PFD5
#define PFDL6_PFD6 _pfdl6.bit._PFD6
#define PFDL6_PFD7 _pfdl6.bit._PFD7
__IO_EXTENDED PFDH6STR _pfdh6;  
#define PFDH6 _pfdh6.byte
#define PFDH6_PFD8 _pfdh6.bit._PFD8
#define PFDH6_PFD9 _pfdh6.bit._PFD9
#define PFDH6_PFD10 _pfdh6.bit._PFD10
#define PFDH6_PFD11 _pfdh6.bit._PFD11
#define PFDH6_PFD12 _pfdh6.bit._PFD12
#define PFDH6_PFD13 _pfdh6.bit._PFD13
#define PFDH6_PFD14 _pfdh6.bit._PFD14
#define PFDH6_PFD15 _pfdh6.bit._PFD15
__IO_EXTENDED PFD7STR _pfd7;  
#define PFD7 _pfd7.word
#define PFD7_PFD0 _pfd7.bit._PFD0
#define PFD7_PFD1 _pfd7.bit._PFD1
#define PFD7_PFD2 _pfd7.bit._PFD2
#define PFD7_PFD3 _pfd7.bit._PFD3
#define PFD7_PFD4 _pfd7.bit._PFD4
#define PFD7_PFD5 _pfd7.bit._PFD5
#define PFD7_PFD6 _pfd7.bit._PFD6
#define PFD7_PFD7 _pfd7.bit._PFD7
#define PFD7_PFD8 _pfd7.bit._PFD8
#define PFD7_PFD9 _pfd7.bit._PFD9
#define PFD7_PFD10 _pfd7.bit._PFD10
#define PFD7_PFD11 _pfd7.bit._PFD11
#define PFD7_PFD12 _pfd7.bit._PFD12
#define PFD7_PFD13 _pfd7.bit._PFD13
#define PFD7_PFD14 _pfd7.bit._PFD14
#define PFD7_PFD15 _pfd7.bit._PFD15
#define PFD7_PFD _pfd7.bitc._PFD
__IO_EXTENDED PFDL7STR _pfdl7;  
#define PFDL7 _pfdl7.byte
#define PFDL7_PFD0 _pfdl7.bit._PFD0
#define PFDL7_PFD1 _pfdl7.bit._PFD1
#define PFDL7_PFD2 _pfdl7.bit._PFD2
#define PFDL7_PFD3 _pfdl7.bit._PFD3
#define PFDL7_PFD4 _pfdl7.bit._PFD4
#define PFDL7_PFD5 _pfdl7.bit._PFD5
#define PFDL7_PFD6 _pfdl7.bit._PFD6
#define PFDL7_PFD7 _pfdl7.bit._PFD7
__IO_EXTENDED PFDH7STR _pfdh7;  
#define PFDH7 _pfdh7.byte
#define PFDH7_PFD8 _pfdh7.bit._PFD8
#define PFDH7_PFD9 _pfdh7.bit._PFD9
#define PFDH7_PFD10 _pfdh7.bit._PFD10
#define PFDH7_PFD11 _pfdh7.bit._PFD11
#define PFDH7_PFD12 _pfdh7.bit._PFD12
#define PFDH7_PFD13 _pfdh7.bit._PFD13
#define PFDH7_PFD14 _pfdh7.bit._PFD14
#define PFDH7_PFD15 _pfdh7.bit._PFD15
__IO_EXTENDED MFMCSSTR _mfmcs;  
#define MFMCS _mfmcs.byte
#define MFMCS_RDY _mfmcs.bit._RDY
#define MFMCS_RDYINT _mfmcs.bit._RDYINT
#define MFMCS_INTE _mfmcs.bit._INTE
#define MFMCS_WE _mfmcs.bit._WE
#define MFMCS_CRBE _mfmcs.bit._CRBE
#define MFMCS_DRBE _mfmcs.bit._DRBE
#define MFMCS_RD19V _mfmcs.bit._RD19V
__IO_EXTENDED MFMTCSTR _mfmtc;  
#define MFMTC _mfmtc.word
#define MFMTC_FAWC0 _mfmtc.bit._FAWC0
#define MFMTC_FAWC1 _mfmtc.bit._FAWC1
#define MFMTC_FAWC2 _mfmtc.bit._FAWC2
#define MFMTC_SYNC _mfmtc.bit._SYNC
#define MFMTC_ADS _mfmtc.bit._ADS
#define MFMTC_CLKBW _mfmtc.bit._CLKBW
#define MFMTC_WEXL _mfmtc.bit._WEXL
#define MFMTC_ATDINIT _mfmtc.bit._ATDINIT
#define MFMTC_ATDL0 _mfmtc.bit._ATDL0
#define MFMTC_ATDL1 _mfmtc.bit._ATDL1
#define MFMTC_ATDEQD0 _mfmtc.bit._ATDEQD0
#define MFMTC_ATDEQD1 _mfmtc.bit._ATDEQD1
#define MFMTC_EQL0 _mfmtc.bit._EQL0
#define MFMTC_EQL1 _mfmtc.bit._EQL1
#define MFMTC_EQL2 _mfmtc.bit._EQL2
#define MFMTC_FAWC _mfmtc.bitc._FAWC
#define MFMTC_ATDL _mfmtc.bitc._ATDL
#define MFMTC_ATDEQD _mfmtc.bitc._ATDEQD
#define MFMTC_EQL _mfmtc.bitc._EQL
__IO_EXTENDED MFMTCLSTR _mfmtcl;  
#define MFMTCL _mfmtcl.byte
#define MFMTCL_FAWC0 _mfmtcl.bit._FAWC0
#define MFMTCL_FAWC1 _mfmtcl.bit._FAWC1
#define MFMTCL_FAWC2 _mfmtcl.bit._FAWC2
#define MFMTCL_SYNC _mfmtcl.bit._SYNC
#define MFMTCL_ADS _mfmtcl.bit._ADS
#define MFMTCL_CLKBW _mfmtcl.bit._CLKBW
#define MFMTCL_WEXL _mfmtcl.bit._WEXL
#define MFMTCL_FAWC _mfmtcl.bitc._FAWC
__IO_EXTENDED MFMTCHSTR _mfmtch;  
#define MFMTCH _mfmtch.byte
#define MFMTCH_ATDINIT _mfmtch.bit._ATDINIT
#define MFMTCH_ATDL0 _mfmtch.bit._ATDL0
#define MFMTCH_ATDL1 _mfmtch.bit._ATDL1
#define MFMTCH_ATDEQD0 _mfmtch.bit._ATDEQD0
#define MFMTCH_ATDEQD1 _mfmtch.bit._ATDEQD1
#define MFMTCH_EQL0 _mfmtch.bit._EQL0
#define MFMTCH_EQL1 _mfmtch.bit._EQL1
#define MFMTCH_EQL2 _mfmtch.bit._EQL2
#define MFMTCH_ATDL _mfmtch.bitc._ATDL
#define MFMTCH_ATDEQD _mfmtch.bitc._ATDEQD
#define MFMTCH_EQL _mfmtch.bitc._EQL
__IO_EXTENDED SFMCSSTR _sfmcs;  
#define SFMCS _sfmcs.byte
#define SFMCS_RDY _sfmcs.bit._RDY
#define SFMCS_RDYINT _sfmcs.bit._RDYINT
#define SFMCS_INTE _sfmcs.bit._INTE
#define SFMCS_WE _sfmcs.bit._WE
#define SFMCS_CRBE _sfmcs.bit._CRBE
#define SFMCS_DRBE _sfmcs.bit._DRBE
#define SFMCS_RD19V _sfmcs.bit._RD19V
__IO_EXTENDED SFMTCSTR _sfmtc;  
#define SFMTC _sfmtc.word
#define SFMTC_FAWC0 _sfmtc.bit._FAWC0
#define SFMTC_FAWC1 _sfmtc.bit._FAWC1
#define SFMTC_FAWC2 _sfmtc.bit._FAWC2
#define SFMTC_SYNC _sfmtc.bit._SYNC
#define SFMTC_ADS _sfmtc.bit._ADS
#define SFMTC_CLKBW _sfmtc.bit._CLKBW
#define SFMTC_WEXL _sfmtc.bit._WEXL
#define SFMTC_ATDINIT _sfmtc.bit._ATDINIT
#define SFMTC_ATDL0 _sfmtc.bit._ATDL0
#define SFMTC_ATDL1 _sfmtc.bit._ATDL1
#define SFMTC_ATDEQD0 _sfmtc.bit._ATDEQD0
#define SFMTC_ATDEQD1 _sfmtc.bit._ATDEQD1
#define SFMTC_EQL0 _sfmtc.bit._EQL0
#define SFMTC_EQL1 _sfmtc.bit._EQL1
#define SFMTC_EQL2 _sfmtc.bit._EQL2
#define SFMTC_FAWC _sfmtc.bitc._FAWC
#define SFMTC_ATDL _sfmtc.bitc._ATDL
#define SFMTC_ATDEQD _sfmtc.bitc._ATDEQD
#define SFMTC_EQL _sfmtc.bitc._EQL
__IO_EXTENDED SFMTCLSTR _sfmtcl;  
#define SFMTCL _sfmtcl.byte
#define SFMTCL_FAWC0 _sfmtcl.bit._FAWC0
#define SFMTCL_FAWC1 _sfmtcl.bit._FAWC1
#define SFMTCL_FAWC2 _sfmtcl.bit._FAWC2
#define SFMTCL_SYNC _sfmtcl.bit._SYNC
#define SFMTCL_ADS _sfmtcl.bit._ADS
#define SFMTCL_CLKBW _sfmtcl.bit._CLKBW
#define SFMTCL_WEXL _sfmtcl.bit._WEXL
#define SFMTCL_FAWC _sfmtcl.bitc._FAWC
__IO_EXTENDED SFMTCHSTR _sfmtch;  
#define SFMTCH _sfmtch.byte
#define SFMTCH_ATDINIT _sfmtch.bit._ATDINIT
#define SFMTCH_ATDL0 _sfmtch.bit._ATDL0
#define SFMTCH_ATDL1 _sfmtch.bit._ATDL1
#define SFMTCH_ATDEQD0 _sfmtch.bit._ATDEQD0
#define SFMTCH_ATDEQD1 _sfmtch.bit._ATDEQD1
#define SFMTCH_EQL0 _sfmtch.bit._EQL0
#define SFMTCH_EQL1 _sfmtch.bit._EQL1
#define SFMTCH_EQL2 _sfmtch.bit._EQL2
#define SFMTCH_ATDL _sfmtch.bitc._ATDL
#define SFMTCH_ATDEQD _sfmtch.bitc._ATDEQD
#define SFMTCH_EQL _sfmtch.bitc._EQL
__IO_EXTENDED FMWC0STR _fmwc0;  
#define FMWC0 _fmwc0.byte
#define FMWC0_WCB0 _fmwc0.bit._WCB0
#define FMWC0_WCB1 _fmwc0.bit._WCB1
#define FMWC0_WCB2 _fmwc0.bit._WCB2
#define FMWC0_WCB3 _fmwc0.bit._WCB3
#define FMWC0_WCB _fmwc0.bitc._WCB
__IO_EXTENDED FMWC1STR _fmwc1;  
#define FMWC1 _fmwc1.byte
#define FMWC1_WCA0 _fmwc1.bit._WCA0
#define FMWC1_WCA1 _fmwc1.bit._WCA1
#define FMWC1_WCA2 _fmwc1.bit._WCA2
#define FMWC1_WCA3 _fmwc1.bit._WCA3
#define FMWC1_WCA _fmwc1.bitc._WCA
__IO_EXTENDED IO_BYTE _fmwc2;
#define FMWC2 _fmwc2   
__IO_EXTENDED IO_BYTE _fmwc3;
#define FMWC3 _fmwc3   
__IO_EXTENDED IO_BYTE _fmwc4;
#define FMWC4 _fmwc4   
__IO_EXTENDED FMWC5STR _fmwc5;  
#define FMWC5 _fmwc5.byte
#define FMWC5_WC32 _fmwc5.bit._WC32
#define FMWC5_WC33 _fmwc5.bit._WC33
#define FMWC5_WC34 _fmwc5.bit._WC34
#define FMWC5_WC35 _fmwc5.bit._WC35
#define FMWC5_WC36 _fmwc5.bit._WC36
#define FMWC5_WC37 _fmwc5.bit._WC37
#define FMWC5_WC38 _fmwc5.bit._WC38
#define FMWC5_WC39 _fmwc5.bit._WC39
#define FMWC5_WC3 _fmwc5.bitc._WC3
__IO_EXTENDED SMCRSTR _smcr;  
#define SMCR _smcr.byte
#define SMCR_SMS0 _smcr.bit._SMS0
#define SMCR_SMS1 _smcr.bit._SMS1
#define SMCR_SPL _smcr.bit._SPL
#define SMCR_SMS _smcr.bitc._SMS
__IO_EXTENDED CKSRSTR _cksr;  
#define CKSR _cksr.byte
#define CKSR_SC1S0 _cksr.bit._SC1S0
#define CKSR_SC1S1 _cksr.bit._SC1S1
#define CKSR_SC2S0 _cksr.bit._SC2S0
#define CKSR_SC2S1 _cksr.bit._SC2S1
#define CKSR_RCE _cksr.bit._RCE
#define CKSR_MCE _cksr.bit._MCE
#define CKSR_PCE _cksr.bit._PCE
#define CKSR_SC1S _cksr.bitc._SC1S
#define CKSR_SC2S _cksr.bitc._SC2S
__IO_EXTENDED CKSSRSTR _ckssr;  
#define CKSSR _ckssr.byte
#define CKSSR_MCST0 _ckssr.bit._MCST0
#define CKSSR_MCST1 _ckssr.bit._MCST1
#define CKSSR_MCST2 _ckssr.bit._MCST2
#define CKSSR_PCST _ckssr.bit._PCST
#define CKSSR_MRFBE _ckssr.bit._MRFBE
#define CKSSR_MCST _ckssr.bitc._MCST
__IO_EXTENDED CKMRSTR _ckmr;  
#define CKMR _ckmr.byte
#define CKMR_SC1M0 _ckmr.bit._SC1M0
#define CKMR_SC1M1 _ckmr.bit._SC1M1
#define CKMR_SC2M0 _ckmr.bit._SC2M0
#define CKMR_SC2M1 _ckmr.bit._SC2M1
#define CKMR_RCM _ckmr.bit._RCM
#define CKMR_MCM _ckmr.bit._MCM
#define CKMR_PCM _ckmr.bit._PCM
#define CKMR_SC1M _ckmr.bitc._SC1M
#define CKMR_SC2M _ckmr.bitc._SC2M
__IO_EXTENDED CKFCRSTR _ckfcr;  
#define CKFCR _ckfcr.word
#define CKFCR_RCFS _ckfcr.bit._RCFS
#define CKFCR_BCD0 _ckfcr.bit._BCD0
#define CKFCR_BCD1 _ckfcr.bit._BCD1
#define CKFCR_BCD2 _ckfcr.bit._BCD2
#define CKFCR_BCD3 _ckfcr.bit._BCD3
#define CKFCR_PC1D0 _ckfcr.bit._PC1D0
#define CKFCR_PC1D1 _ckfcr.bit._PC1D1
#define CKFCR_PC1D2 _ckfcr.bit._PC1D2
#define CKFCR_PC1D3 _ckfcr.bit._PC1D3
#define CKFCR_PC2D0 _ckfcr.bit._PC2D0
#define CKFCR_PC2D1 _ckfcr.bit._PC2D1
#define CKFCR_PC2D2 _ckfcr.bit._PC2D2
#define CKFCR_PC2D3 _ckfcr.bit._PC2D3
#define CKFCR_BCD _ckfcr.bitc._BCD
#define CKFCR_PC1D _ckfcr.bitc._PC1D
#define CKFCR_PC2D _ckfcr.bitc._PC2D
__IO_EXTENDED CKFCRLSTR _ckfcrl;  
#define CKFCRL _ckfcrl.byte
#define CKFCRL_RCFS _ckfcrl.bit._RCFS
#define CKFCRL_BCD0 _ckfcrl.bit._BCD0
#define CKFCRL_BCD1 _ckfcrl.bit._BCD1
#define CKFCRL_BCD2 _ckfcrl.bit._BCD2
#define CKFCRL_BCD3 _ckfcrl.bit._BCD3
#define CKFCRL_BCD _ckfcrl.bitc._BCD
__IO_EXTENDED CKFCRHSTR _ckfcrh;  
#define CKFCRH _ckfcrh.byte
#define CKFCRH_PC1D0 _ckfcrh.bit._PC1D0
#define CKFCRH_PC1D1 _ckfcrh.bit._PC1D1
#define CKFCRH_PC1D2 _ckfcrh.bit._PC1D2
#define CKFCRH_PC1D3 _ckfcrh.bit._PC1D3
#define CKFCRH_PC2D0 _ckfcrh.bit._PC2D0
#define CKFCRH_PC2D1 _ckfcrh.bit._PC2D1
#define CKFCRH_PC2D2 _ckfcrh.bit._PC2D2
#define CKFCRH_PC2D3 _ckfcrh.bit._PC2D3
#define CKFCRH_PC1D _ckfcrh.bitc._PC1D
#define CKFCRH_PC2D _ckfcrh.bitc._PC2D
__IO_EXTENDED PLLCRSTR _pllcr;  
#define PLLCR _pllcr.word
#define PLLCR_PMS0 _pllcr.bit._PMS0
#define PLLCR_PMS1 _pllcr.bit._PMS1
#define PLLCR_PMS2 _pllcr.bit._PMS2
#define PLLCR_PMS3 _pllcr.bit._PMS3
#define PLLCR_PMS4 _pllcr.bit._PMS4
#define PLLCR_VMS0 _pllcr.bit._VMS0
#define PLLCR_VMS1 _pllcr.bit._VMS1
#define PLLCR_VMS2 _pllcr.bit._VMS2
#define PLLCR_PC3D0 _pllcr.bit._PC3D0
#define PLLCR_PC3D1 _pllcr.bit._PC3D1
#define PLLCR_PC3D2 _pllcr.bit._PC3D2
#define PLLCR_PC3D3 _pllcr.bit._PC3D3
#define PLLCR_PMS _pllcr.bitc._PMS
#define PLLCR_VMS _pllcr.bitc._VMS
#define PLLCR_PC3D _pllcr.bitc._PC3D
__IO_EXTENDED PLLCRLSTR _pllcrl;  
#define PLLCRL _pllcrl.byte
#define PLLCRL_PMS0 _pllcrl.bit._PMS0
#define PLLCRL_PMS1 _pllcrl.bit._PMS1
#define PLLCRL_PMS2 _pllcrl.bit._PMS2
#define PLLCRL_PMS3 _pllcrl.bit._PMS3
#define PLLCRL_PMS4 _pllcrl.bit._PMS4
#define PLLCRL_VMS0 _pllcrl.bit._VMS0
#define PLLCRL_VMS1 _pllcrl.bit._VMS1
#define PLLCRL_VMS2 _pllcrl.bit._VMS2
#define PLLCRL_PMS _pllcrl.bitc._PMS
#define PLLCRL_VMS _pllcrl.bitc._VMS
__IO_EXTENDED PLLCRHSTR _pllcrh;  
#define PLLCRH _pllcrh.byte
#define PLLCRH_PC3D0 _pllcrh.bit._PC3D0
#define PLLCRH_PC3D1 _pllcrh.bit._PC3D1
#define PLLCRH_PC3D2 _pllcrh.bit._PC3D2
#define PLLCRH_PC3D3 _pllcrh.bit._PC3D3
#define PLLCRH_PC3D _pllcrh.bitc._PC3D
__IO_EXTENDED RCTCRSTR _rctcr;  
#define RCTCR _rctcr.byte
#define RCTCR_RCTI0 _rctcr.bit._RCTI0
#define RCTCR_RCTI1 _rctcr.bit._RCTI1
#define RCTCR_RCTI2 _rctcr.bit._RCTI2
#define RCTCR_RCTI3 _rctcr.bit._RCTI3
#define RCTCR_RCTR _rctcr.bit._RCTR
#define RCTCR_RCTIF _rctcr.bit._RCTIF
#define RCTCR_RCTIE _rctcr.bit._RCTIE
#define RCTCR_RCTI _rctcr.bitc._RCTI
__IO_EXTENDED MCTCRSTR _mctcr;  
#define MCTCR _mctcr.byte
#define MCTCR_MCTI0 _mctcr.bit._MCTI0
#define MCTCR_MCTI1 _mctcr.bit._MCTI1
#define MCTCR_MCTI2 _mctcr.bit._MCTI2
#define MCTCR_MCTI3 _mctcr.bit._MCTI3
#define MCTCR_MCTR _mctcr.bit._MCTR
#define MCTCR_MCTIF _mctcr.bit._MCTIF
#define MCTCR_MCTIE _mctcr.bit._MCTIE
#define MCTCR_MCTI _mctcr.bitc._MCTI
__IO_EXTENDED RCCSRCSTR _rccsrc;  
#define RCCSRC _rccsrc.byte
#define RCCSRC_PRST _rccsrc.bit._PRST
#define RCCSRC_ERST _rccsrc.bit._ERST
#define RCCSRC_MCRST _rccsrc.bit._MCRST
#define RCCSRC_SRST _rccsrc.bit._SRST
#define RCCSRC_WRST _rccsrc.bit._WRST
#define RCCSRC_MCMF _rccsrc.bit._MCMF
__IO_EXTENDED RCRSTR _rcr;  
#define RCR _rcr.byte
#define RCR_SRSTG _rcr.bit._SRSTG
#define RCR_LVRE _rcr.bit._LVRE
#define RCR_LVDE _rcr.bit._LVDE
#define RCR_CSDRE _rcr.bit._CSDRE
#define RCR_MCSDI _rcr.bit._MCSDI
__IO_EXTENDED RCCSRSTR _rccsr;  
#define RCCSR _rccsr.byte
#define RCCSR_PRST _rccsr.bit._PRST
#define RCCSR_ERST _rccsr.bit._ERST
#define RCCSR_MCRST _rccsr.bit._MCRST
#define RCCSR_SRST _rccsr.bit._SRST
#define RCCSR_WRST _rccsr.bit._WRST
#define RCCSR_MCMF _rccsr.bit._MCMF
__IO_EXTENDED WDTCSTR _wdtc;  
#define WDTC _wdtc.byte
#define WDTC_WTI0 _wdtc.bit._WTI0
#define WDTC_WTI1 _wdtc.bit._WTI1
#define WDTC_WTI2 _wdtc.bit._WTI2
#define WDTC_WTI3 _wdtc.bit._WTI3
#define WDTC_WTCS0 _wdtc.bit._WTCS0
#define WDTC_WTCS1 _wdtc.bit._WTCS1
#define WDTC_RSTP _wdtc.bit._RSTP
#define WDTC_WTI _wdtc.bitc._WTI
#define WDTC_WTCS _wdtc.bitc._WTCS
__IO_EXTENDED WDTCPSTR _wdtcp;  
#define WDTCP _wdtcp.byte
#define WDTCP_WCP0 _wdtcp.bit._WCP0
#define WDTCP_WCP1 _wdtcp.bit._WCP1
#define WDTCP_WCP2 _wdtcp.bit._WCP2
#define WDTCP_WCP3 _wdtcp.bit._WCP3
#define WDTCP_WCP4 _wdtcp.bit._WCP4
#define WDTCP_WCP5 _wdtcp.bit._WCP5
#define WDTCP_WCP6 _wdtcp.bit._WCP6
#define WDTCP_WCP7 _wdtcp.bit._WCP7
#define WDTCP_WCP _wdtcp.bitc._WCP
__IO_EXTENDED COARSTR _coar;  
#define COAR _coar.byte
#define COAR_CKOE0 _coar.bit._CKOE0
#define COAR_CKOXE0 _coar.bit._CKOXE0
#define COAR_RUNC0 _coar.bit._RUNC0
#define COAR_RUNM0 _coar.bit._RUNM0
#define COAR_CKOE1 _coar.bit._CKOE1
#define COAR_CKOXE1 _coar.bit._CKOXE1
#define COAR_RUNC1 _coar.bit._RUNC1
#define COAR_RUNM1 _coar.bit._RUNM1
__IO_EXTENDED COCR0STR _cocr0;  
#define COCR0 _cocr0.byte
#define COCR0_SEL0 _cocr0.bit._SEL0
#define COCR0_SEL1 _cocr0.bit._SEL1
#define COCR0_SEL2 _cocr0.bit._SEL2
#define COCR0_SEL3 _cocr0.bit._SEL3
#define COCR0_DIV0 _cocr0.bit._DIV0
#define COCR0_DIV1 _cocr0.bit._DIV1
#define COCR0_DIV2 _cocr0.bit._DIV2
#define COCR0_SEL _cocr0.bitc._SEL
#define COCR0_DIV _cocr0.bitc._DIV
__IO_EXTENDED COCR1STR _cocr1;  
#define COCR1 _cocr1.byte
#define COCR1_SEL0 _cocr1.bit._SEL0
#define COCR1_SEL1 _cocr1.bit._SEL1
#define COCR1_SEL2 _cocr1.bit._SEL2
#define COCR1_SEL3 _cocr1.bit._SEL3
#define COCR1_DIV0 _cocr1.bit._DIV0
#define COCR1_DIV1 _cocr1.bit._DIV1
#define COCR1_DIV2 _cocr1.bit._DIV2
#define COCR1_SEL _cocr1.bitc._SEL
#define COCR1_DIV _cocr1.bitc._DIV
__IO_EXTENDED CMCRSTR _cmcr;  
#define CMCR _cmcr.byte
#define CMCR_PDX _cmcr.bit._PDX
#define CMCR_MODEN _cmcr.bit._MODEN
#define CMCR_MODRUN _cmcr.bit._MODRUN
__IO_EXTENDED CMPRSTR _cmpr;  
#define CMPR _cmpr.word
#define CMPR_C0 _cmpr.bit._C0
#define CMPR_C1 _cmpr.bit._C1
#define CMPR_C2 _cmpr.bit._C2
#define CMPR_C3 _cmpr.bit._C3
#define CMPR_C4 _cmpr.bit._C4
#define CMPR_N0 _cmpr.bit._N0
#define CMPR_N1 _cmpr.bit._N1
#define CMPR_N2 _cmpr.bit._N2
#define CMPR_N3 _cmpr.bit._N3
#define CMPR_K0 _cmpr.bit._K0
#define CMPR_K1 _cmpr.bit._K1
#define CMPR_K2 _cmpr.bit._K2
#define CMPR_K3 _cmpr.bit._K3
#define CMPR_K4 _cmpr.bit._K4
#define CMPR_C _cmpr.bitc._C
#define CMPR_N _cmpr.bitc._N
#define CMPR_K _cmpr.bitc._K
__IO_EXTENDED CMPRLSTR _cmprl;  
#define CMPRL _cmprl.byte
#define CMPRL_C0 _cmprl.bit._C0
#define CMPRL_C1 _cmprl.bit._C1
#define CMPRL_C2 _cmprl.bit._C2
#define CMPRL_C3 _cmprl.bit._C3
#define CMPRL_C4 _cmprl.bit._C4
#define CMPRL_N0 _cmprl.bit._N0
#define CMPRL_N1 _cmprl.bit._N1
#define CMPRL_N2 _cmprl.bit._N2
#define CMPRL_C _cmprl.bitc._C
#define CMPRL_N _cmprl.bitc._N
__IO_EXTENDED CMPRHSTR _cmprh;  
#define CMPRH _cmprh.byte
#define CMPRH_N3 _cmprh.bit._N3
#define CMPRH_K0 _cmprh.bit._K0
#define CMPRH_K1 _cmprh.bit._K1
#define CMPRH_K2 _cmprh.bit._K2
#define CMPRH_K3 _cmprh.bit._K3
#define CMPRH_K4 _cmprh.bit._K4
#define CMPRH_K _cmprh.bitc._K
__IO_EXTENDED VRCRSTR _vrcr;  
#define VRCR _vrcr.byte
#define VRCR_LPBM0 _vrcr.bit._LPBM0
#define VRCR_LPBM1 _vrcr.bit._LPBM1
#define VRCR_LPMB2 _vrcr.bit._LPMB2
#define VRCR_LPMA0 _vrcr.bit._LPMA0
#define VRCR_LPMA1 _vrcr.bit._LPMA1
#define VRCR_LPMA2 _vrcr.bit._LPMA2
#define VRCR_HPM0 _vrcr.bit._HPM0
#define VRCR_HPM1 _vrcr.bit._HPM1
#define VRCR_LPBM _vrcr.bitc._LPBM
#define VRCR_LPMA _vrcr.bitc._LPMA
#define VRCR_HPM _vrcr.bitc._HPM
__IO_EXTENDED DDR00STR _ddr00;  
#define DDR00 _ddr00.byte
#define DDR00_D0 _ddr00.bit._D0
#define DDR00_D1 _ddr00.bit._D1
#define DDR00_D2 _ddr00.bit._D2
#define DDR00_D3 _ddr00.bit._D3
#define DDR00_D4 _ddr00.bit._D4
#define DDR00_D5 _ddr00.bit._D5
#define DDR00_D6 _ddr00.bit._D6
#define DDR00_D7 _ddr00.bit._D7
__IO_EXTENDED DDR01STR _ddr01;  
#define DDR01 _ddr01.byte
#define DDR01_D0 _ddr01.bit._D0
#define DDR01_D1 _ddr01.bit._D1
#define DDR01_D2 _ddr01.bit._D2
#define DDR01_D3 _ddr01.bit._D3
#define DDR01_D4 _ddr01.bit._D4
#define DDR01_D5 _ddr01.bit._D5
#define DDR01_D6 _ddr01.bit._D6
#define DDR01_D7 _ddr01.bit._D7
__IO_EXTENDED DDR02STR _ddr02;  
#define DDR02 _ddr02.byte
#define DDR02_D0 _ddr02.bit._D0
#define DDR02_D1 _ddr02.bit._D1
#define DDR02_D2 _ddr02.bit._D2
#define DDR02_D3 _ddr02.bit._D3
#define DDR02_D4 _ddr02.bit._D4
#define DDR02_D5 _ddr02.bit._D5
#define DDR02_D6 _ddr02.bit._D6
#define DDR02_D7 _ddr02.bit._D7
__IO_EXTENDED DDR03STR _ddr03;  
#define DDR03 _ddr03.byte
#define DDR03_D0 _ddr03.bit._D0
#define DDR03_D1 _ddr03.bit._D1
#define DDR03_D2 _ddr03.bit._D2
#define DDR03_D3 _ddr03.bit._D3
#define DDR03_D4 _ddr03.bit._D4
#define DDR03_D5 _ddr03.bit._D5
#define DDR03_D6 _ddr03.bit._D6
#define DDR03_D7 _ddr03.bit._D7
__IO_EXTENDED DDR04STR _ddr04;  
#define DDR04 _ddr04.byte
#define DDR04_D0 _ddr04.bit._D0
#define DDR04_D1 _ddr04.bit._D1
#define DDR04_D2 _ddr04.bit._D2
#define DDR04_D3 _ddr04.bit._D3
#define DDR04_D4 _ddr04.bit._D4
#define DDR04_D5 _ddr04.bit._D5
#define DDR04_D6 _ddr04.bit._D6
#define DDR04_D7 _ddr04.bit._D7
__IO_EXTENDED DDR05STR _ddr05;  
#define DDR05 _ddr05.byte
#define DDR05_D0 _ddr05.bit._D0
#define DDR05_D1 _ddr05.bit._D1
#define DDR05_D2 _ddr05.bit._D2
#define DDR05_D3 _ddr05.bit._D3
#define DDR05_D4 _ddr05.bit._D4
#define DDR05_D5 _ddr05.bit._D5
#define DDR05_D6 _ddr05.bit._D6
#define DDR05_D7 _ddr05.bit._D7
__IO_EXTENDED DDR06STR _ddr06;  
#define DDR06 _ddr06.byte
#define DDR06_D0 _ddr06.bit._D0
#define DDR06_D1 _ddr06.bit._D1
#define DDR06_D2 _ddr06.bit._D2
#define DDR06_D3 _ddr06.bit._D3
#define DDR06_D4 _ddr06.bit._D4
#define DDR06_D5 _ddr06.bit._D5
#define DDR06_D6 _ddr06.bit._D6
#define DDR06_D7 _ddr06.bit._D7
__IO_EXTENDED DDR07STR _ddr07;  
#define DDR07 _ddr07.byte
#define DDR07_D0 _ddr07.bit._D0
#define DDR07_D1 _ddr07.bit._D1
#define DDR07_D2 _ddr07.bit._D2
#define DDR07_D3 _ddr07.bit._D3
#define DDR07_D4 _ddr07.bit._D4
#define DDR07_D5 _ddr07.bit._D5
#define DDR07_D6 _ddr07.bit._D6
#define DDR07_D7 _ddr07.bit._D7
__IO_EXTENDED DDR08STR _ddr08;  
#define DDR08 _ddr08.byte
#define DDR08_D0 _ddr08.bit._D0
#define DDR08_D1 _ddr08.bit._D1
#define DDR08_D2 _ddr08.bit._D2
#define DDR08_D3 _ddr08.bit._D3
#define DDR08_D4 _ddr08.bit._D4
#define DDR08_D5 _ddr08.bit._D5
#define DDR08_D6 _ddr08.bit._D6
#define DDR08_D7 _ddr08.bit._D7
__IO_EXTENDED DDR09STR _ddr09;  
#define DDR09 _ddr09.byte
#define DDR09_D0 _ddr09.bit._D0
#define DDR09_D1 _ddr09.bit._D1
#define DDR09_D2 _ddr09.bit._D2
#define DDR09_D3 _ddr09.bit._D3
#define DDR09_D4 _ddr09.bit._D4
#define DDR09_D5 _ddr09.bit._D5
#define DDR09_D6 _ddr09.bit._D6
#define DDR09_D7 _ddr09.bit._D7
__IO_EXTENDED DDR10STR _ddr10;  
#define DDR10 _ddr10.byte
#define DDR10_D0 _ddr10.bit._D0
#define DDR10_D1 _ddr10.bit._D1
__IO_EXTENDED PIER00STR _pier00;  
#define PIER00 _pier00.byte
#define PIER00_IE0 _pier00.bit._IE0
#define PIER00_IE1 _pier00.bit._IE1
#define PIER00_IE2 _pier00.bit._IE2
#define PIER00_IE3 _pier00.bit._IE3
#define PIER00_IE4 _pier00.bit._IE4
#define PIER00_IE5 _pier00.bit._IE5
#define PIER00_IE6 _pier00.bit._IE6
#define PIER00_IE7 _pier00.bit._IE7
__IO_EXTENDED PIER01STR _pier01;  
#define PIER01 _pier01.byte
#define PIER01_IE0 _pier01.bit._IE0
#define PIER01_IE1 _pier01.bit._IE1
#define PIER01_IE2 _pier01.bit._IE2
#define PIER01_IE3 _pier01.bit._IE3
#define PIER01_IE4 _pier01.bit._IE4
#define PIER01_IE5 _pier01.bit._IE5
#define PIER01_IE6 _pier01.bit._IE6
#define PIER01_IE7 _pier01.bit._IE7
__IO_EXTENDED PIER02STR _pier02;  
#define PIER02 _pier02.byte
#define PIER02_IE0 _pier02.bit._IE0
#define PIER02_IE1 _pier02.bit._IE1
#define PIER02_IE2 _pier02.bit._IE2
#define PIER02_IE3 _pier02.bit._IE3
#define PIER02_IE4 _pier02.bit._IE4
#define PIER02_IE5 _pier02.bit._IE5
#define PIER02_IE6 _pier02.bit._IE6
#define PIER02_IE7 _pier02.bit._IE7
__IO_EXTENDED PIER03STR _pier03;  
#define PIER03 _pier03.byte
#define PIER03_IE0 _pier03.bit._IE0
#define PIER03_IE1 _pier03.bit._IE1
#define PIER03_IE2 _pier03.bit._IE2
#define PIER03_IE3 _pier03.bit._IE3
#define PIER03_IE4 _pier03.bit._IE4
#define PIER03_IE5 _pier03.bit._IE5
#define PIER03_IE6 _pier03.bit._IE6
#define PIER03_IE7 _pier03.bit._IE7
__IO_EXTENDED PIER04STR _pier04;  
#define PIER04 _pier04.byte
#define PIER04_IE0 _pier04.bit._IE0
#define PIER04_IE1 _pier04.bit._IE1
#define PIER04_IE2 _pier04.bit._IE2
#define PIER04_IE3 _pier04.bit._IE3
#define PIER04_IE4 _pier04.bit._IE4
#define PIER04_IE5 _pier04.bit._IE5
#define PIER04_IE6 _pier04.bit._IE6
#define PIER04_IE7 _pier04.bit._IE7
__IO_EXTENDED PIER05STR _pier05;  
#define PIER05 _pier05.byte
#define PIER05_IE0 _pier05.bit._IE0
#define PIER05_IE1 _pier05.bit._IE1
#define PIER05_IE2 _pier05.bit._IE2
#define PIER05_IE3 _pier05.bit._IE3
#define PIER05_IE4 _pier05.bit._IE4
#define PIER05_IE5 _pier05.bit._IE5
#define PIER05_IE6 _pier05.bit._IE6
#define PIER05_IE7 _pier05.bit._IE7
__IO_EXTENDED PIER06STR _pier06;  
#define PIER06 _pier06.byte
#define PIER06_IE0 _pier06.bit._IE0
#define PIER06_IE1 _pier06.bit._IE1
#define PIER06_IE2 _pier06.bit._IE2
#define PIER06_IE3 _pier06.bit._IE3
#define PIER06_IE4 _pier06.bit._IE4
#define PIER06_IE5 _pier06.bit._IE5
#define PIER06_IE6 _pier06.bit._IE6
#define PIER06_IE7 _pier06.bit._IE7
__IO_EXTENDED PIER07STR _pier07;  
#define PIER07 _pier07.byte
#define PIER07_IE0 _pier07.bit._IE0
#define PIER07_IE1 _pier07.bit._IE1
#define PIER07_IE2 _pier07.bit._IE2
#define PIER07_IE3 _pier07.bit._IE3
#define PIER07_IE4 _pier07.bit._IE4
#define PIER07_IE5 _pier07.bit._IE5
#define PIER07_IE6 _pier07.bit._IE6
#define PIER07_IE7 _pier07.bit._IE7
__IO_EXTENDED PIER08STR _pier08;  
#define PIER08 _pier08.byte
#define PIER08_IE0 _pier08.bit._IE0
#define PIER08_IE1 _pier08.bit._IE1
#define PIER08_IE2 _pier08.bit._IE2
#define PIER08_IE3 _pier08.bit._IE3
#define PIER08_IE4 _pier08.bit._IE4
#define PIER08_IE5 _pier08.bit._IE5
#define PIER08_IE6 _pier08.bit._IE6
#define PIER08_IE7 _pier08.bit._IE7
__IO_EXTENDED PIER09STR _pier09;  
#define PIER09 _pier09.byte
#define PIER09_IE0 _pier09.bit._IE0
#define PIER09_IE1 _pier09.bit._IE1
#define PIER09_IE2 _pier09.bit._IE2
#define PIER09_IE3 _pier09.bit._IE3
#define PIER09_IE4 _pier09.bit._IE4
#define PIER09_IE5 _pier09.bit._IE5
#define PIER09_IE6 _pier09.bit._IE6
#define PIER09_IE7 _pier09.bit._IE7
__IO_EXTENDED PIER10STR _pier10;  
#define PIER10 _pier10.byte
#define PIER10_IE0 _pier10.bit._IE0
#define PIER10_IE1 _pier10.bit._IE1
__IO_EXTENDED PILR00STR _pilr00;  
#define PILR00 _pilr00.byte
#define PILR00_IL0 _pilr00.bit._IL0
#define PILR00_IL1 _pilr00.bit._IL1
#define PILR00_IL2 _pilr00.bit._IL2
#define PILR00_IL3 _pilr00.bit._IL3
#define PILR00_IL4 _pilr00.bit._IL4
#define PILR00_IL5 _pilr00.bit._IL5
#define PILR00_IL6 _pilr00.bit._IL6
#define PILR00_IL7 _pilr00.bit._IL7
__IO_EXTENDED PILR01STR _pilr01;  
#define PILR01 _pilr01.byte
#define PILR01_IL0 _pilr01.bit._IL0
#define PILR01_IL1 _pilr01.bit._IL1
#define PILR01_IL2 _pilr01.bit._IL2
#define PILR01_IL3 _pilr01.bit._IL3
#define PILR01_IL4 _pilr01.bit._IL4
#define PILR01_IL5 _pilr01.bit._IL5
#define PILR01_IL6 _pilr01.bit._IL6
#define PILR01_IL7 _pilr01.bit._IL7
__IO_EXTENDED PILR02STR _pilr02;  
#define PILR02 _pilr02.byte
#define PILR02_IL0 _pilr02.bit._IL0
#define PILR02_IL1 _pilr02.bit._IL1
#define PILR02_IL2 _pilr02.bit._IL2
#define PILR02_IL3 _pilr02.bit._IL3
#define PILR02_IL4 _pilr02.bit._IL4
#define PILR02_IL5 _pilr02.bit._IL5
#define PILR02_IL6 _pilr02.bit._IL6
#define PILR02_IL7 _pilr02.bit._IL7
__IO_EXTENDED PILR03STR _pilr03;  
#define PILR03 _pilr03.byte
#define PILR03_IL0 _pilr03.bit._IL0
#define PILR03_IL1 _pilr03.bit._IL1
#define PILR03_IL2 _pilr03.bit._IL2
#define PILR03_IL3 _pilr03.bit._IL3
#define PILR03_IL4 _pilr03.bit._IL4
#define PILR03_IL5 _pilr03.bit._IL5
#define PILR03_IL6 _pilr03.bit._IL6
#define PILR03_IL7 _pilr03.bit._IL7
__IO_EXTENDED PILR04STR _pilr04;  
#define PILR04 _pilr04.byte
#define PILR04_IL0 _pilr04.bit._IL0
#define PILR04_IL1 _pilr04.bit._IL1
#define PILR04_IL2 _pilr04.bit._IL2
#define PILR04_IL3 _pilr04.bit._IL3
#define PILR04_IL4 _pilr04.bit._IL4
#define PILR04_IL5 _pilr04.bit._IL5
#define PILR04_IL6 _pilr04.bit._IL6
#define PILR04_IL7 _pilr04.bit._IL7
__IO_EXTENDED PILR05STR _pilr05;  
#define PILR05 _pilr05.byte
#define PILR05_IL0 _pilr05.bit._IL0
#define PILR05_IL1 _pilr05.bit._IL1
#define PILR05_IL2 _pilr05.bit._IL2
#define PILR05_IL3 _pilr05.bit._IL3
#define PILR05_IL4 _pilr05.bit._IL4
#define PILR05_IL5 _pilr05.bit._IL5
#define PILR05_IL6 _pilr05.bit._IL6
#define PILR05_IL7 _pilr05.bit._IL7
__IO_EXTENDED PILR06STR _pilr06;  
#define PILR06 _pilr06.byte
#define PILR06_IL0 _pilr06.bit._IL0
#define PILR06_IL1 _pilr06.bit._IL1
#define PILR06_IL2 _pilr06.bit._IL2
#define PILR06_IL3 _pilr06.bit._IL3
#define PILR06_IL4 _pilr06.bit._IL4
#define PILR06_IL5 _pilr06.bit._IL5
#define PILR06_IL6 _pilr06.bit._IL6
#define PILR06_IL7 _pilr06.bit._IL7
__IO_EXTENDED PILR07STR _pilr07;  
#define PILR07 _pilr07.byte
#define PILR07_IL0 _pilr07.bit._IL0
#define PILR07_IL1 _pilr07.bit._IL1
#define PILR07_IL2 _pilr07.bit._IL2
#define PILR07_IL3 _pilr07.bit._IL3
#define PILR07_IL4 _pilr07.bit._IL4
#define PILR07_IL5 _pilr07.bit._IL5
#define PILR07_IL6 _pilr07.bit._IL6
#define PILR07_IL7 _pilr07.bit._IL7
__IO_EXTENDED PILR08STR _pilr08;  
#define PILR08 _pilr08.byte
#define PILR08_IL0 _pilr08.bit._IL0
#define PILR08_IL1 _pilr08.bit._IL1
#define PILR08_IL2 _pilr08.bit._IL2
#define PILR08_IL3 _pilr08.bit._IL3
#define PILR08_IL4 _pilr08.bit._IL4
#define PILR08_IL5 _pilr08.bit._IL5
#define PILR08_IL6 _pilr08.bit._IL6
#define PILR08_IL7 _pilr08.bit._IL7
__IO_EXTENDED PILR09STR _pilr09;  
#define PILR09 _pilr09.byte
#define PILR09_IL0 _pilr09.bit._IL0
#define PILR09_IL1 _pilr09.bit._IL1
#define PILR09_IL2 _pilr09.bit._IL2
#define PILR09_IL3 _pilr09.bit._IL3
#define PILR09_IL4 _pilr09.bit._IL4
#define PILR09_IL5 _pilr09.bit._IL5
#define PILR09_IL6 _pilr09.bit._IL6
#define PILR09_IL7 _pilr09.bit._IL7
__IO_EXTENDED PILR10STR _pilr10;  
#define PILR10 _pilr10.byte
#define PILR10_IL0 _pilr10.bit._IL0
#define PILR10_IL1 _pilr10.bit._IL1
__IO_EXTENDED EPILR00STR _epilr00;  
#define EPILR00 _epilr00.byte
#define EPILR00_EIL0 _epilr00.bit._EIL0
#define EPILR00_EIL1 _epilr00.bit._EIL1
#define EPILR00_EIL2 _epilr00.bit._EIL2
#define EPILR00_EIL3 _epilr00.bit._EIL3
#define EPILR00_EIL4 _epilr00.bit._EIL4
#define EPILR00_EIL5 _epilr00.bit._EIL5
#define EPILR00_EIL6 _epilr00.bit._EIL6
#define EPILR00_EIL7 _epilr00.bit._EIL7
__IO_EXTENDED EPILR01STR _epilr01;  
#define EPILR01 _epilr01.byte
#define EPILR01_EIL0 _epilr01.bit._EIL0
#define EPILR01_EIL1 _epilr01.bit._EIL1
#define EPILR01_EIL2 _epilr01.bit._EIL2
#define EPILR01_EIL3 _epilr01.bit._EIL3
#define EPILR01_EIL4 _epilr01.bit._EIL4
#define EPILR01_EIL5 _epilr01.bit._EIL5
#define EPILR01_EIL6 _epilr01.bit._EIL6
#define EPILR01_EIL7 _epilr01.bit._EIL7
__IO_EXTENDED EPILR02STR _epilr02;  
#define EPILR02 _epilr02.byte
#define EPILR02_EIL0 _epilr02.bit._EIL0
#define EPILR02_EIL1 _epilr02.bit._EIL1
#define EPILR02_EIL2 _epilr02.bit._EIL2
#define EPILR02_EIL3 _epilr02.bit._EIL3
#define EPILR02_EIL4 _epilr02.bit._EIL4
#define EPILR02_EIL5 _epilr02.bit._EIL5
#define EPILR02_EIL6 _epilr02.bit._EIL6
#define EPILR02_EIL7 _epilr02.bit._EIL7
__IO_EXTENDED EPILR03STR _epilr03;  
#define EPILR03 _epilr03.byte
#define EPILR03_EIL0 _epilr03.bit._EIL0
#define EPILR03_EIL1 _epilr03.bit._EIL1
#define EPILR03_EIL2 _epilr03.bit._EIL2
#define EPILR03_EIL3 _epilr03.bit._EIL3
#define EPILR03_EIL4 _epilr03.bit._EIL4
#define EPILR03_EIL5 _epilr03.bit._EIL5
#define EPILR03_EIL6 _epilr03.bit._EIL6
#define EPILR03_EIL7 _epilr03.bit._EIL7
__IO_EXTENDED EPILR04STR _epilr04;  
#define EPILR04 _epilr04.byte
#define EPILR04_EIL0 _epilr04.bit._EIL0
#define EPILR04_EIL1 _epilr04.bit._EIL1
#define EPILR04_EIL2 _epilr04.bit._EIL2
#define EPILR04_EIL3 _epilr04.bit._EIL3
#define EPILR04_EIL4 _epilr04.bit._EIL4
#define EPILR04_EIL5 _epilr04.bit._EIL5
#define EPILR04_EIL6 _epilr04.bit._EIL6
#define EPILR04_EIL7 _epilr04.bit._EIL7
__IO_EXTENDED EPILR05STR _epilr05;  
#define EPILR05 _epilr05.byte
#define EPILR05_EIL0 _epilr05.bit._EIL0
#define EPILR05_EIL1 _epilr05.bit._EIL1
#define EPILR05_EIL2 _epilr05.bit._EIL2
#define EPILR05_EIL3 _epilr05.bit._EIL3
#define EPILR05_EIL4 _epilr05.bit._EIL4
#define EPILR05_EIL5 _epilr05.bit._EIL5
#define EPILR05_EIL6 _epilr05.bit._EIL6
#define EPILR05_EIL7 _epilr05.bit._EIL7
__IO_EXTENDED EPILR06STR _epilr06;  
#define EPILR06 _epilr06.byte
#define EPILR06_EIL0 _epilr06.bit._EIL0
#define EPILR06_EIL1 _epilr06.bit._EIL1
#define EPILR06_EIL2 _epilr06.bit._EIL2
#define EPILR06_EIL3 _epilr06.bit._EIL3
#define EPILR06_EIL4 _epilr06.bit._EIL4
#define EPILR06_EIL5 _epilr06.bit._EIL5
#define EPILR06_EIL6 _epilr06.bit._EIL6
#define EPILR06_EIL7 _epilr06.bit._EIL7
__IO_EXTENDED EPILR07STR _epilr07;  
#define EPILR07 _epilr07.byte
#define EPILR07_EIL0 _epilr07.bit._EIL0
#define EPILR07_EIL1 _epilr07.bit._EIL1
#define EPILR07_EIL2 _epilr07.bit._EIL2
#define EPILR07_EIL3 _epilr07.bit._EIL3
#define EPILR07_EIL4 _epilr07.bit._EIL4
#define EPILR07_EIL5 _epilr07.bit._EIL5
#define EPILR07_EIL6 _epilr07.bit._EIL6
#define EPILR07_EIL7 _epilr07.bit._EIL7
__IO_EXTENDED EPILR08STR _epilr08;  
#define EPILR08 _epilr08.byte
#define EPILR08_EIL0 _epilr08.bit._EIL0
#define EPILR08_EIL1 _epilr08.bit._EIL1
#define EPILR08_EIL2 _epilr08.bit._EIL2
#define EPILR08_EIL3 _epilr08.bit._EIL3
#define EPILR08_EIL4 _epilr08.bit._EIL4
#define EPILR08_EIL5 _epilr08.bit._EIL5
#define EPILR08_EIL6 _epilr08.bit._EIL6
#define EPILR08_EIL7 _epilr08.bit._EIL7
__IO_EXTENDED EPILR09STR _epilr09;  
#define EPILR09 _epilr09.byte
#define EPILR09_EIL0 _epilr09.bit._EIL0
#define EPILR09_EIL1 _epilr09.bit._EIL1
#define EPILR09_EIL2 _epilr09.bit._EIL2
#define EPILR09_EIL3 _epilr09.bit._EIL3
#define EPILR09_EIL4 _epilr09.bit._EIL4
#define EPILR09_EIL5 _epilr09.bit._EIL5
#define EPILR09_EIL6 _epilr09.bit._EIL6
#define EPILR09_EIL7 _epilr09.bit._EIL7
__IO_EXTENDED EPILR10STR _epilr10;  
#define EPILR10 _epilr10.byte
#define EPILR10_EIL0 _epilr10.bit._EIL0
#define EPILR10_EIL1 _epilr10.bit._EIL1
__IO_EXTENDED PODR00STR _podr00;  
#define PODR00 _podr00.byte
#define PODR00_OD0 _podr00.bit._OD0
#define PODR00_OD1 _podr00.bit._OD1
#define PODR00_OD2 _podr00.bit._OD2
#define PODR00_OD3 _podr00.bit._OD3
#define PODR00_OD4 _podr00.bit._OD4
#define PODR00_OD5 _podr00.bit._OD5
#define PODR00_OD6 _podr00.bit._OD6
#define PODR00_OD7 _podr00.bit._OD7
__IO_EXTENDED PODR01STR _podr01;  
#define PODR01 _podr01.byte
#define PODR01_OD0 _podr01.bit._OD0
#define PODR01_OD1 _podr01.bit._OD1
#define PODR01_OD2 _podr01.bit._OD2
#define PODR01_OD3 _podr01.bit._OD3
#define PODR01_OD4 _podr01.bit._OD4
#define PODR01_OD5 _podr01.bit._OD5
#define PODR01_OD6 _podr01.bit._OD6
#define PODR01_OD7 _podr01.bit._OD7
__IO_EXTENDED PODR02STR _podr02;  
#define PODR02 _podr02.byte
#define PODR02_OD0 _podr02.bit._OD0
#define PODR02_OD1 _podr02.bit._OD1
#define PODR02_OD2 _podr02.bit._OD2
#define PODR02_OD3 _podr02.bit._OD3
#define PODR02_OD4 _podr02.bit._OD4
#define PODR02_OD5 _podr02.bit._OD5
#define PODR02_OD6 _podr02.bit._OD6
#define PODR02_OD7 _podr02.bit._OD7
__IO_EXTENDED PODR03STR _podr03;  
#define PODR03 _podr03.byte
#define PODR03_OD0 _podr03.bit._OD0
#define PODR03_OD1 _podr03.bit._OD1
#define PODR03_OD2 _podr03.bit._OD2
#define PODR03_OD3 _podr03.bit._OD3
#define PODR03_OD4 _podr03.bit._OD4
#define PODR03_OD5 _podr03.bit._OD5
#define PODR03_OD6 _podr03.bit._OD6
#define PODR03_OD7 _podr03.bit._OD7
__IO_EXTENDED PODR04STR _podr04;  
#define PODR04 _podr04.byte
#define PODR04_OD0 _podr04.bit._OD0
#define PODR04_OD1 _podr04.bit._OD1
#define PODR04_OD2 _podr04.bit._OD2
#define PODR04_OD3 _podr04.bit._OD3
#define PODR04_OD4 _podr04.bit._OD4
#define PODR04_OD5 _podr04.bit._OD5
#define PODR04_OD6 _podr04.bit._OD6
#define PODR04_OD7 _podr04.bit._OD7
__IO_EXTENDED PODR05STR _podr05;  
#define PODR05 _podr05.byte
#define PODR05_OD0 _podr05.bit._OD0
#define PODR05_OD1 _podr05.bit._OD1
#define PODR05_OD2 _podr05.bit._OD2
#define PODR05_OD3 _podr05.bit._OD3
#define PODR05_OD4 _podr05.bit._OD4
#define PODR05_OD5 _podr05.bit._OD5
#define PODR05_OD6 _podr05.bit._OD6
#define PODR05_OD7 _podr05.bit._OD7
__IO_EXTENDED PODR06STR _podr06;  
#define PODR06 _podr06.byte
#define PODR06_OD0 _podr06.bit._OD0
#define PODR06_OD1 _podr06.bit._OD1
#define PODR06_OD2 _podr06.bit._OD2
#define PODR06_OD3 _podr06.bit._OD3
#define PODR06_OD4 _podr06.bit._OD4
#define PODR06_OD5 _podr06.bit._OD5
#define PODR06_OD6 _podr06.bit._OD6
#define PODR06_OD7 _podr06.bit._OD7
__IO_EXTENDED PODR07STR _podr07;  
#define PODR07 _podr07.byte
#define PODR07_OD0 _podr07.bit._OD0
#define PODR07_OD1 _podr07.bit._OD1
#define PODR07_OD2 _podr07.bit._OD2
#define PODR07_OD3 _podr07.bit._OD3
#define PODR07_OD4 _podr07.bit._OD4
#define PODR07_OD5 _podr07.bit._OD5
#define PODR07_OD6 _podr07.bit._OD6
#define PODR07_OD7 _podr07.bit._OD7
__IO_EXTENDED PODR08STR _podr08;  
#define PODR08 _podr08.byte
#define PODR08_OD0 _podr08.bit._OD0
#define PODR08_OD1 _podr08.bit._OD1
#define PODR08_OD2 _podr08.bit._OD2
#define PODR08_OD3 _podr08.bit._OD3
#define PODR08_OD4 _podr08.bit._OD4
#define PODR08_OD5 _podr08.bit._OD5
#define PODR08_OD6 _podr08.bit._OD6
#define PODR08_OD7 _podr08.bit._OD7
__IO_EXTENDED PODR09STR _podr09;  
#define PODR09 _podr09.byte
#define PODR09_OD0 _podr09.bit._OD0
#define PODR09_OD1 _podr09.bit._OD1
#define PODR09_OD2 _podr09.bit._OD2
#define PODR09_OD3 _podr09.bit._OD3
#define PODR09_OD4 _podr09.bit._OD4
#define PODR09_OD5 _podr09.bit._OD5
#define PODR09_OD6 _podr09.bit._OD6
#define PODR09_OD7 _podr09.bit._OD7
__IO_EXTENDED PODR10STR _podr10;  
#define PODR10 _podr10.byte
#define PODR10_OD0 _podr10.bit._OD0
#define PODR10_OD1 _podr10.bit._OD1
__IO_EXTENDED PHDR08STR _phdr08;  
#define PHDR08 _phdr08.byte
#define PHDR08_HD0 _phdr08.bit._HD0
#define PHDR08_HD1 _phdr08.bit._HD1
#define PHDR08_HD2 _phdr08.bit._HD2
#define PHDR08_HD3 _phdr08.bit._HD3
#define PHDR08_HD4 _phdr08.bit._HD4
#define PHDR08_HD5 _phdr08.bit._HD5
#define PHDR08_HD6 _phdr08.bit._HD6
#define PHDR08_HD7 _phdr08.bit._HD7
__IO_EXTENDED PHDR09STR _phdr09;  
#define PHDR09 _phdr09.byte
#define PHDR09_HD0 _phdr09.bit._HD0
#define PHDR09_HD1 _phdr09.bit._HD1
#define PHDR09_HD2 _phdr09.bit._HD2
#define PHDR09_HD3 _phdr09.bit._HD3
#define PHDR09_HD4 _phdr09.bit._HD4
#define PHDR09_HD5 _phdr09.bit._HD5
#define PHDR09_HD6 _phdr09.bit._HD6
#define PHDR09_HD7 _phdr09.bit._HD7
__IO_EXTENDED PHDR10STR _phdr10;  
#define PHDR10 _phdr10.byte
#define PHDR10_HD0 _phdr10.bit._HD0
#define PHDR10_HD1 _phdr10.bit._HD1
#define PHDR10_HD2 _phdr10.bit._HD2
#define PHDR10_HD3 _phdr10.bit._HD3
#define PHDR10_HD4 _phdr10.bit._HD4
#define PHDR10_HD5 _phdr10.bit._HD5
#define PHDR10_HD6 _phdr10.bit._HD6
#define PHDR10_HD7 _phdr10.bit._HD7
__IO_EXTENDED PUCR00STR _pucr00;  
#define PUCR00 _pucr00.byte
#define PUCR00_PU0 _pucr00.bit._PU0
#define PUCR00_PU1 _pucr00.bit._PU1
#define PUCR00_PU2 _pucr00.bit._PU2
#define PUCR00_PU3 _pucr00.bit._PU3
#define PUCR00_PU4 _pucr00.bit._PU4
#define PUCR00_PU5 _pucr00.bit._PU5
#define PUCR00_PU6 _pucr00.bit._PU6
#define PUCR00_PU7 _pucr00.bit._PU7
__IO_EXTENDED PUCR01STR _pucr01;  
#define PUCR01 _pucr01.byte
#define PUCR01_PU0 _pucr01.bit._PU0
#define PUCR01_PU1 _pucr01.bit._PU1
#define PUCR01_PU2 _pucr01.bit._PU2
#define PUCR01_PU3 _pucr01.bit._PU3
#define PUCR01_PU4 _pucr01.bit._PU4
#define PUCR01_PU5 _pucr01.bit._PU5
#define PUCR01_PU6 _pucr01.bit._PU6
#define PUCR01_PU7 _pucr01.bit._PU7
__IO_EXTENDED PUCR02STR _pucr02;  
#define PUCR02 _pucr02.byte
#define PUCR02_PU0 _pucr02.bit._PU0
#define PUCR02_PU1 _pucr02.bit._PU1
#define PUCR02_PU2 _pucr02.bit._PU2
#define PUCR02_PU3 _pucr02.bit._PU3
#define PUCR02_PU4 _pucr02.bit._PU4
#define PUCR02_PU5 _pucr02.bit._PU5
#define PUCR02_PU6 _pucr02.bit._PU6
#define PUCR02_PU7 _pucr02.bit._PU7
__IO_EXTENDED PUCR03STR _pucr03;  
#define PUCR03 _pucr03.byte
#define PUCR03_PU0 _pucr03.bit._PU0
#define PUCR03_PU1 _pucr03.bit._PU1
#define PUCR03_PU2 _pucr03.bit._PU2
#define PUCR03_PU3 _pucr03.bit._PU3
#define PUCR03_PU4 _pucr03.bit._PU4
#define PUCR03_PU5 _pucr03.bit._PU5
#define PUCR03_PU6 _pucr03.bit._PU6
#define PUCR03_PU7 _pucr03.bit._PU7
__IO_EXTENDED PUCR04STR _pucr04;  
#define PUCR04 _pucr04.byte
#define PUCR04_PU0 _pucr04.bit._PU0
#define PUCR04_PU1 _pucr04.bit._PU1
#define PUCR04_PU2 _pucr04.bit._PU2
#define PUCR04_PU3 _pucr04.bit._PU3
#define PUCR04_PU4 _pucr04.bit._PU4
#define PUCR04_PU5 _pucr04.bit._PU5
#define PUCR04_PU6 _pucr04.bit._PU6
#define PUCR04_PU7 _pucr04.bit._PU7
__IO_EXTENDED PUCR05STR _pucr05;  
#define PUCR05 _pucr05.byte
#define PUCR05_PU0 _pucr05.bit._PU0
#define PUCR05_PU1 _pucr05.bit._PU1
#define PUCR05_PU2 _pucr05.bit._PU2
#define PUCR05_PU3 _pucr05.bit._PU3
#define PUCR05_PU4 _pucr05.bit._PU4
#define PUCR05_PU5 _pucr05.bit._PU5
#define PUCR05_PU6 _pucr05.bit._PU6
#define PUCR05_PU7 _pucr05.bit._PU7
__IO_EXTENDED PUCR06STR _pucr06;  
#define PUCR06 _pucr06.byte
#define PUCR06_PU0 _pucr06.bit._PU0
#define PUCR06_PU1 _pucr06.bit._PU1
#define PUCR06_PU2 _pucr06.bit._PU2
#define PUCR06_PU3 _pucr06.bit._PU3
#define PUCR06_PU4 _pucr06.bit._PU4
#define PUCR06_PU5 _pucr06.bit._PU5
#define PUCR06_PU6 _pucr06.bit._PU6
#define PUCR06_PU7 _pucr06.bit._PU7
__IO_EXTENDED PUCR07STR _pucr07;  
#define PUCR07 _pucr07.byte
#define PUCR07_PU0 _pucr07.bit._PU0
#define PUCR07_PU1 _pucr07.bit._PU1
#define PUCR07_PU2 _pucr07.bit._PU2
#define PUCR07_PU3 _pucr07.bit._PU3
#define PUCR07_PU4 _pucr07.bit._PU4
#define PUCR07_PU5 _pucr07.bit._PU5
#define PUCR07_PU6 _pucr07.bit._PU6
#define PUCR07_PU7 _pucr07.bit._PU7
__IO_EXTENDED PUCR08STR _pucr08;  
#define PUCR08 _pucr08.byte
#define PUCR08_PU0 _pucr08.bit._PU0
#define PUCR08_PU1 _pucr08.bit._PU1
#define PUCR08_PU2 _pucr08.bit._PU2
#define PUCR08_PU3 _pucr08.bit._PU3
#define PUCR08_PU4 _pucr08.bit._PU4
#define PUCR08_PU5 _pucr08.bit._PU5
#define PUCR08_PU6 _pucr08.bit._PU6
#define PUCR08_PU7 _pucr08.bit._PU7
__IO_EXTENDED PUCR09STR _pucr09;  
#define PUCR09 _pucr09.byte
#define PUCR09_PU0 _pucr09.bit._PU0
#define PUCR09_PU1 _pucr09.bit._PU1
#define PUCR09_PU2 _pucr09.bit._PU2
#define PUCR09_PU3 _pucr09.bit._PU3
#define PUCR09_PU4 _pucr09.bit._PU4
#define PUCR09_PU5 _pucr09.bit._PU5
#define PUCR09_PU6 _pucr09.bit._PU6
#define PUCR09_PU7 _pucr09.bit._PU7
__IO_EXTENDED PUCR10STR _pucr10;  
#define PUCR10 _pucr10.byte
#define PUCR10_PU0 _pucr10.bit._PU0
#define PUCR10_PU1 _pucr10.bit._PU1
__IO_EXTENDED EPSR00STR _epsr00;  
#define EPSR00 _epsr00.byte
#define EPSR00_PS0 _epsr00.bit._PS0
#define EPSR00_PS1 _epsr00.bit._PS1
#define EPSR00_PS2 _epsr00.bit._PS2
#define EPSR00_PS3 _epsr00.bit._PS3
#define EPSR00_PS4 _epsr00.bit._PS4
#define EPSR00_PS5 _epsr00.bit._PS5
#define EPSR00_PS6 _epsr00.bit._PS6
#define EPSR00_PS7 _epsr00.bit._PS7
__IO_EXTENDED EPSR01STR _epsr01;  
#define EPSR01 _epsr01.byte
#define EPSR01_PS0 _epsr01.bit._PS0
#define EPSR01_PS1 _epsr01.bit._PS1
#define EPSR01_PS2 _epsr01.bit._PS2
#define EPSR01_PS3 _epsr01.bit._PS3
#define EPSR01_PS4 _epsr01.bit._PS4
#define EPSR01_PS5 _epsr01.bit._PS5
#define EPSR01_PS6 _epsr01.bit._PS6
#define EPSR01_PS7 _epsr01.bit._PS7
__IO_EXTENDED EPSR02STR _epsr02;  
#define EPSR02 _epsr02.byte
#define EPSR02_PS0 _epsr02.bit._PS0
#define EPSR02_PS1 _epsr02.bit._PS1
#define EPSR02_PS2 _epsr02.bit._PS2
#define EPSR02_PS3 _epsr02.bit._PS3
#define EPSR02_PS4 _epsr02.bit._PS4
#define EPSR02_PS5 _epsr02.bit._PS5
#define EPSR02_PS6 _epsr02.bit._PS6
#define EPSR02_PS7 _epsr02.bit._PS7
__IO_EXTENDED EPSR03STR _epsr03;  
#define EPSR03 _epsr03.byte
#define EPSR03_PS0 _epsr03.bit._PS0
#define EPSR03_PS1 _epsr03.bit._PS1
#define EPSR03_PS2 _epsr03.bit._PS2
#define EPSR03_PS3 _epsr03.bit._PS3
#define EPSR03_PS4 _epsr03.bit._PS4
#define EPSR03_PS5 _epsr03.bit._PS5
#define EPSR03_PS6 _epsr03.bit._PS6
#define EPSR03_PS7 _epsr03.bit._PS7
__IO_EXTENDED EPSR04STR _epsr04;  
#define EPSR04 _epsr04.byte
#define EPSR04_PS0 _epsr04.bit._PS0
#define EPSR04_PS1 _epsr04.bit._PS1
#define EPSR04_PS2 _epsr04.bit._PS2
#define EPSR04_PS3 _epsr04.bit._PS3
#define EPSR04_PS4 _epsr04.bit._PS4
#define EPSR04_PS5 _epsr04.bit._PS5
#define EPSR04_PS6 _epsr04.bit._PS6
#define EPSR04_PS7 _epsr04.bit._PS7
__IO_EXTENDED EPSR05STR _epsr05;  
#define EPSR05 _epsr05.byte
#define EPSR05_PS0 _epsr05.bit._PS0
#define EPSR05_PS1 _epsr05.bit._PS1
#define EPSR05_PS2 _epsr05.bit._PS2
#define EPSR05_PS3 _epsr05.bit._PS3
#define EPSR05_PS4 _epsr05.bit._PS4
#define EPSR05_PS5 _epsr05.bit._PS5
#define EPSR05_PS6 _epsr05.bit._PS6
#define EPSR05_PS7 _epsr05.bit._PS7
__IO_EXTENDED EPSR06STR _epsr06;  
#define EPSR06 _epsr06.byte
#define EPSR06_PS0 _epsr06.bit._PS0
#define EPSR06_PS1 _epsr06.bit._PS1
#define EPSR06_PS2 _epsr06.bit._PS2
#define EPSR06_PS3 _epsr06.bit._PS3
#define EPSR06_PS4 _epsr06.bit._PS4
#define EPSR06_PS5 _epsr06.bit._PS5
#define EPSR06_PS6 _epsr06.bit._PS6
#define EPSR06_PS7 _epsr06.bit._PS7
__IO_EXTENDED EPSR07STR _epsr07;  
#define EPSR07 _epsr07.byte
#define EPSR07_PS0 _epsr07.bit._PS0
#define EPSR07_PS1 _epsr07.bit._PS1
#define EPSR07_PS2 _epsr07.bit._PS2
#define EPSR07_PS3 _epsr07.bit._PS3
#define EPSR07_PS4 _epsr07.bit._PS4
#define EPSR07_PS5 _epsr07.bit._PS5
#define EPSR07_PS6 _epsr07.bit._PS6
#define EPSR07_PS7 _epsr07.bit._PS7
__IO_EXTENDED EPSR08STR _epsr08;  
#define EPSR08 _epsr08.byte
#define EPSR08_PS0 _epsr08.bit._PS0
#define EPSR08_PS1 _epsr08.bit._PS1
#define EPSR08_PS2 _epsr08.bit._PS2
#define EPSR08_PS3 _epsr08.bit._PS3
#define EPSR08_PS4 _epsr08.bit._PS4
#define EPSR08_PS5 _epsr08.bit._PS5
#define EPSR08_PS6 _epsr08.bit._PS6
#define EPSR08_PS7 _epsr08.bit._PS7
__IO_EXTENDED EPSR09STR _epsr09;  
#define EPSR09 _epsr09.byte
#define EPSR09_PS0 _epsr09.bit._PS0
#define EPSR09_PS1 _epsr09.bit._PS1
#define EPSR09_PS2 _epsr09.bit._PS2
#define EPSR09_PS3 _epsr09.bit._PS3
#define EPSR09_PS4 _epsr09.bit._PS4
#define EPSR09_PS5 _epsr09.bit._PS5
#define EPSR09_PS6 _epsr09.bit._PS6
#define EPSR09_PS7 _epsr09.bit._PS7
__IO_EXTENDED EPSR10STR _epsr10;  
#define EPSR10 _epsr10.byte
#define EPSR10_PS0 _epsr10.bit._PS0
#define EPSR10_PS1 _epsr10.bit._PS1
__IO_EXTENDED ADER0STR _ader0;  
#define ADER0 _ader0.byte
#define ADER0_ADE0 _ader0.bit._ADE0
#define ADER0_ADE1 _ader0.bit._ADE1
#define ADER0_ADE2 _ader0.bit._ADE2
#define ADER0_ADE3 _ader0.bit._ADE3
#define ADER0_ADE4 _ader0.bit._ADE4
#define ADER0_ADE5 _ader0.bit._ADE5
#define ADER0_ADE6 _ader0.bit._ADE6
#define ADER0_ADE7 _ader0.bit._ADE7
__IO_EXTENDED ADER1STR _ader1;  
#define ADER1 _ader1.byte
#define ADER1_ADE8 _ader1.bit._ADE8
#define ADER1_ADE9 _ader1.bit._ADE9
#define ADER1_ADE10 _ader1.bit._ADE10
#define ADER1_ADE11 _ader1.bit._ADE11
#define ADER1_ADE12 _ader1.bit._ADE12
#define ADER1_ADE13 _ader1.bit._ADE13
#define ADER1_ADE14 _ader1.bit._ADE14
#define ADER1_ADE15 _ader1.bit._ADE15
__IO_EXTENDED ADER2STR _ader2;  
#define ADER2 _ader2.byte
#define ADER2_ADE16 _ader2.bit._ADE16
#define ADER2_ADE17 _ader2.bit._ADE17
#define ADER2_ADE18 _ader2.bit._ADE18
#define ADER2_ADE19 _ader2.bit._ADE19
#define ADER2_ADE20 _ader2.bit._ADE20
#define ADER2_ADE21 _ader2.bit._ADE21
#define ADER2_ADE22 _ader2.bit._ADE22
#define ADER2_ADE23 _ader2.bit._ADE23
__IO_EXTENDED PRRR0STR _prrr0;  
#define PRRR0 _prrr0.byte
#define PRRR0_INT0_R _prrr0.bit._INT0_R
#define PRRR0_INT1_R _prrr0.bit._INT1_R
#define PRRR0_INT2_R _prrr0.bit._INT2_R
#define PRRR0_INT3_R _prrr0.bit._INT3_R
#define PRRR0_INT4_R _prrr0.bit._INT4_R
#define PRRR0_INT5_R _prrr0.bit._INT5_R
#define PRRR0_INT6_R _prrr0.bit._INT6_R
#define PRRR0_INT7_R _prrr0.bit._INT7_R
__IO_EXTENDED PRRR1STR _prrr1;  
#define PRRR1 _prrr1.byte
#define PRRR1_INT8_R _prrr1.bit._INT8_R
#define PRRR1_INT9_R _prrr1.bit._INT9_R
#define PRRR1_INT10_R _prrr1.bit._INT10_R
#define PRRR1_INT11_R _prrr1.bit._INT11_R
#define PRRR1_INT12_R _prrr1.bit._INT12_R
#define PRRR1_INT13_R _prrr1.bit._INT13_R
#define PRRR1_INT14_R _prrr1.bit._INT14_R
#define PRRR1_INT15_R _prrr1.bit._INT15_R
__IO_EXTENDED PRRR2STR _prrr2;  
#define PRRR2 _prrr2.byte
#define PRRR2_PPG0_R _prrr2.bit._PPG0_R
#define PRRR2_PPG1_R _prrr2.bit._PPG1_R
#define PRRR2_PPG2_R _prrr2.bit._PPG2_R
#define PRRR2_PPG3_R _prrr2.bit._PPG3_R
#define PRRR2_PPG4_R _prrr2.bit._PPG4_R
#define PRRR2_PPG5_R _prrr2.bit._PPG5_R
#define PRRR2_PPG6_R _prrr2.bit._PPG6_R
#define PRRR2_PPG7_R _prrr2.bit._PPG7_R
__IO_EXTENDED PRRR3STR _prrr3;  
#define PRRR3 _prrr3.byte
#define PRRR3_TIN0_R _prrr3.bit._TIN0_R
#define PRRR3_TOT0_R _prrr3.bit._TOT0_R
#define PRRR3_TIN1_R _prrr3.bit._TIN1_R
#define PRRR3_TOT1_R _prrr3.bit._TOT1_R
#define PRRR3_TIN2_R _prrr3.bit._TIN2_R
#define PRRR3_TOT2_R _prrr3.bit._TOT2_R
#define PRRR3_TIN3_R _prrr3.bit._TIN3_R
#define PRRR3_TOT3_R _prrr3.bit._TOT3_R
__IO_EXTENDED PRRR4STR _prrr4;  
#define PRRR4 _prrr4.byte
#define PRRR4_IN0_R _prrr4.bit._IN0_R
#define PRRR4_IN1_R _prrr4.bit._IN1_R
#define PRRR4_IN2_R _prrr4.bit._IN2_R
#define PRRR4_IN3_R _prrr4.bit._IN3_R
#define PRRR4_IN4_R _prrr4.bit._IN4_R
#define PRRR4_IN5_R _prrr4.bit._IN5_R
#define PRRR4_IN6_R _prrr4.bit._IN6_R
#define PRRR4_IN7_R _prrr4.bit._IN7_R
__IO_EXTENDED PRRR5STR _prrr5;  
#define PRRR5 _prrr5.byte
#define PRRR5_OUT0_R _prrr5.bit._OUT0_R
#define PRRR5_OUT1_R _prrr5.bit._OUT1_R
#define PRRR5_OUT2_R _prrr5.bit._OUT2_R
#define PRRR5_OUT3_R _prrr5.bit._OUT3_R
#define PRRR5_OUT6_R _prrr5.bit._OUT6_R
#define PRRR5_OUT7_R _prrr5.bit._OUT7_R
__IO_EXTENDED PRRR6STR _prrr6;  
#define PRRR6 _prrr6.byte
#define PRRR6_SGO0_R _prrr6.bit._SGO0_R
#define PRRR6_SGA0_R _prrr6.bit._SGA0_R
#define PRRR6_FRCK0_R _prrr6.bit._FRCK0_R
#define PRRR6_SIN2_R _prrr6.bit._SIN2_R
#define PRRR6_SOT2_R _prrr6.bit._SOT2_R
#define PRRR6_SCK2_R _prrr6.bit._SCK2_R
#define PRRR6_CKOT1_R _prrr6.bit._CKOT1_R
#define PRRR6_CKOTX1_R _prrr6.bit._CKOTX1_R
__IO_EXTENDED PRRR7STR _prrr7;  
#define PRRR7 _prrr7.byte
#define PRRR7_ADTG_R _prrr7.bit._ADTG_R
#define PRRR7_NMI_R _prrr7.bit._NMI_R
#define PRRR7_CS3_R _prrr7.bit._CS3_R
#define PRRR7_INT3_R1 _prrr7.bit._INT3_R1
#define PRRR7_INT4_R1 _prrr7.bit._INT4_R1
#define PRRR7_INT5_R1 _prrr7.bit._INT5_R1
#define PRRR7_RX2_R _prrr7.bit._RX2_R
#define PRRR7_TX2_R _prrr7.bit._TX2_R
__IO_EXTENDED PRRR8STR _prrr8;  
#define PRRR8 _prrr8.byte
#define PRRR8_SIN7_R _prrr8.bit._SIN7_R
#define PRRR8_SOT7_R _prrr8.bit._SOT7_R
#define PRRR8_SCK7_R _prrr8.bit._SCK7_R
#define PRRR8_SIN8_R _prrr8.bit._SIN8_R
#define PRRR8_SOT8_R _prrr8.bit._SOT8_R
#define PRRR8_SCK8_R _prrr8.bit._SCK8_R
#define PRRR8_SIN9_R _prrr8.bit._SIN9_R
#define PRRR8_SOT9_R _prrr8.bit._SOT9_R
__IO_EXTENDED PRRR9STR _prrr9;  
#define PRRR9 _prrr9.byte
#define PRRR9_SCK9_R _prrr9.bit._SCK9_R
#define PRRR9_SGO1_R _prrr9.bit._SGO1_R
#define PRRR9_SGA1_R _prrr9.bit._SGA1_R
#define PRRR9_FRCK2_R _prrr9.bit._FRCK2_R
#define PRRR9_OUT10_R _prrr9.bit._OUT10_R
#define PRRR9_CKOT0_R _prrr9.bit._CKOT0_R
__IO_EXTENDED WTBR0STR _wtbr0;  
#define WTBR0 _wtbr0.word
#define WTBR0_D0 _wtbr0.bit._D0
#define WTBR0_D1 _wtbr0.bit._D1
#define WTBR0_D2 _wtbr0.bit._D2
#define WTBR0_D3 _wtbr0.bit._D3
#define WTBR0_D4 _wtbr0.bit._D4
#define WTBR0_D5 _wtbr0.bit._D5
#define WTBR0_D6 _wtbr0.bit._D6
#define WTBR0_D7 _wtbr0.bit._D7
#define WTBR0_D8 _wtbr0.bit._D8
#define WTBR0_D9 _wtbr0.bit._D9
#define WTBR0_D10 _wtbr0.bit._D10
#define WTBR0_D11 _wtbr0.bit._D11
#define WTBR0_D12 _wtbr0.bit._D12
#define WTBR0_D13 _wtbr0.bit._D13
#define WTBR0_D14 _wtbr0.bit._D14
#define WTBR0_D15 _wtbr0.bit._D15
#define WTBR0_D _wtbr0.bitc._D
__IO_EXTENDED WTBRL0STR _wtbrl0;  
#define WTBRL0 _wtbrl0.byte
#define WTBRL0_D0 _wtbrl0.bit._D0
#define WTBRL0_D1 _wtbrl0.bit._D1
#define WTBRL0_D2 _wtbrl0.bit._D2
#define WTBRL0_D3 _wtbrl0.bit._D3
#define WTBRL0_D4 _wtbrl0.bit._D4
#define WTBRL0_D5 _wtbrl0.bit._D5
#define WTBRL0_D6 _wtbrl0.bit._D6
#define WTBRL0_D7 _wtbrl0.bit._D7
__IO_EXTENDED WTBRH0STR _wtbrh0;  
#define WTBRH0 _wtbrh0.byte
#define WTBRH0_D8 _wtbrh0.bit._D8
#define WTBRH0_D9 _wtbrh0.bit._D9
#define WTBRH0_D10 _wtbrh0.bit._D10
#define WTBRH0_D11 _wtbrh0.bit._D11
#define WTBRH0_D12 _wtbrh0.bit._D12
#define WTBRH0_D13 _wtbrh0.bit._D13
#define WTBRH0_D14 _wtbrh0.bit._D14
#define WTBRH0_D15 _wtbrh0.bit._D15
__IO_EXTENDED WTBR1STR _wtbr1;  
#define WTBR1 _wtbr1.byte
#define WTBR1_D16 _wtbr1.bit._D16
#define WTBR1_D17 _wtbr1.bit._D17
#define WTBR1_D18 _wtbr1.bit._D18
#define WTBR1_D19 _wtbr1.bit._D19
#define WTBR1_D20 _wtbr1.bit._D20
#define WTBR1_D1 _wtbr1.bitc._D1
__IO_EXTENDED WTSRSTR _wtsr;  
#define WTSR _wtsr.byte
#define WTSR_S0 _wtsr.bit._S0
#define WTSR_S1 _wtsr.bit._S1
#define WTSR_S2 _wtsr.bit._S2
#define WTSR_S3 _wtsr.bit._S3
#define WTSR_S4 _wtsr.bit._S4
#define WTSR_S5 _wtsr.bit._S5
#define WTSR_S _wtsr.bitc._S
__IO_EXTENDED WTMRSTR _wtmr;  
#define WTMR _wtmr.byte
#define WTMR_M0 _wtmr.bit._M0
#define WTMR_M1 _wtmr.bit._M1
#define WTMR_M2 _wtmr.bit._M2
#define WTMR_M3 _wtmr.bit._M3
#define WTMR_M4 _wtmr.bit._M4
#define WTMR_M5 _wtmr.bit._M5
#define WTMR_M _wtmr.bitc._M
__IO_EXTENDED WTHRSTR _wthr;  
#define WTHR _wthr.byte
#define WTHR_H0 _wthr.bit._H0
#define WTHR_H1 _wthr.bit._H1
#define WTHR_H2 _wthr.bit._H2
#define WTHR_H3 _wthr.bit._H3
#define WTHR_H4 _wthr.bit._H4
#define WTHR_H _wthr.bitc._H
__IO_EXTENDED WTCERSTR _wtcer;  
#define WTCER _wtcer.byte
#define WTCER_INT4 _wtcer.bit._INT4
#define WTCER_INTE4 _wtcer.bit._INTE4
__IO_EXTENDED WTCKSRSTR _wtcksr;  
#define WTCKSR _wtcksr.byte
#define WTCKSR_CKSEL0 _wtcksr.bit._CKSEL0
#define WTCKSR_CKSEL1 _wtcksr.bit._CKSEL1
#define WTCKSR_CKSEL _wtcksr.bitc._CKSEL
__IO_EXTENDED WTCRSTR _wtcr;  
#define WTCR _wtcr.word
#define WTCR_ST _wtcr.bit._ST
#define WTCR_OE _wtcr.bit._OE
#define WTCR_UPDT _wtcr.bit._UPDT
#define WTCR_RUN _wtcr.bit._RUN
#define WTCR_INT0 _wtcr.bit._INT0
#define WTCR_INTE0 _wtcr.bit._INTE0
#define WTCR_INT1 _wtcr.bit._INT1
#define WTCR_INTE1 _wtcr.bit._INTE1
#define WTCR_INT2 _wtcr.bit._INT2
#define WTCR_INTE2 _wtcr.bit._INTE2
#define WTCR_INT3 _wtcr.bit._INT3
#define WTCR_INTE3 _wtcr.bit._INTE3
__IO_EXTENDED WTCRLSTR _wtcrl;  
#define WTCRL _wtcrl.byte
#define WTCRL_ST _wtcrl.bit._ST
#define WTCRL_OE _wtcrl.bit._OE
#define WTCRL_UPDT _wtcrl.bit._UPDT
#define WTCRL_RUN _wtcrl.bit._RUN
__IO_EXTENDED WTCRHSTR _wtcrh;  
#define WTCRH _wtcrh.byte
#define WTCRH_INT0 _wtcrh.bit._INT0
#define WTCRH_INTE0 _wtcrh.bit._INTE0
#define WTCRH_INT1 _wtcrh.bit._INT1
#define WTCRH_INTE1 _wtcrh.bit._INTE1
#define WTCRH_INT2 _wtcrh.bit._INT2
#define WTCRH_INTE2 _wtcrh.bit._INTE2
#define WTCRH_INT3 _wtcrh.bit._INT3
#define WTCRH_INTE3 _wtcrh.bit._INTE3
__IO_EXTENDED CUCRSTR _cucr;  
#define CUCR _cucr.byte
#define CUCR_INTEN _cucr.bit._INTEN
#define CUCR_INT _cucr.bit._INT
#define CUCR_CKSEL _cucr.bit._CKSEL
#define CUCR_STRT _cucr.bit._STRT
#define CUCR_RESV _cucr.bit._RESV
__IO_EXTENDED CUTDSTR _cutd;  
#define CUTD _cutd.word
#define CUTD_TDD0 _cutd.bit._TDD0
#define CUTD_TDD1 _cutd.bit._TDD1
#define CUTD_TDD2 _cutd.bit._TDD2
#define CUTD_TDD3 _cutd.bit._TDD3
#define CUTD_TDD4 _cutd.bit._TDD4
#define CUTD_TDD5 _cutd.bit._TDD5
#define CUTD_TDD6 _cutd.bit._TDD6
#define CUTD_TDD7 _cutd.bit._TDD7
#define CUTD_TDD8 _cutd.bit._TDD8
#define CUTD_TDD9 _cutd.bit._TDD9
#define CUTD_TDD10 _cutd.bit._TDD10
#define CUTD_TDD11 _cutd.bit._TDD11
#define CUTD_TDD12 _cutd.bit._TDD12
#define CUTD_TDD13 _cutd.bit._TDD13
#define CUTD_TDD14 _cutd.bit._TDD14
#define CUTD_TDD15 _cutd.bit._TDD15
#define CUTD_TDD _cutd.bitc._TDD
__IO_EXTENDED CUTDLSTR _cutdl;  
#define CUTDL _cutdl.byte
#define CUTDL_TDD0 _cutdl.bit._TDD0
#define CUTDL_TDD1 _cutdl.bit._TDD1
#define CUTDL_TDD2 _cutdl.bit._TDD2
#define CUTDL_TDD3 _cutdl.bit._TDD3
#define CUTDL_TDD4 _cutdl.bit._TDD4
#define CUTDL_TDD5 _cutdl.bit._TDD5
#define CUTDL_TDD6 _cutdl.bit._TDD6
#define CUTDL_TDD7 _cutdl.bit._TDD7
__IO_EXTENDED CUTDHSTR _cutdh;  
#define CUTDH _cutdh.byte
#define CUTDH_TDD8 _cutdh.bit._TDD8
#define CUTDH_TDD9 _cutdh.bit._TDD9
#define CUTDH_TDD10 _cutdh.bit._TDD10
#define CUTDH_TDD11 _cutdh.bit._TDD11
#define CUTDH_TDD12 _cutdh.bit._TDD12
#define CUTDH_TDD13 _cutdh.bit._TDD13
#define CUTDH_TDD14 _cutdh.bit._TDD14
#define CUTDH_TDD15 _cutdh.bit._TDD15
__IO_EXTENDED CUTRSTR _cutr;  
#define CUTR _cutr.lword
#define CUTR_TDR0 _cutr.bit._TDR0
#define CUTR_TDR1 _cutr.bit._TDR1
#define CUTR_TDR2 _cutr.bit._TDR2
#define CUTR_TDR3 _cutr.bit._TDR3
#define CUTR_TDR4 _cutr.bit._TDR4
#define CUTR_TDR5 _cutr.bit._TDR5
#define CUTR_TDR6 _cutr.bit._TDR6
#define CUTR_TDR7 _cutr.bit._TDR7
#define CUTR_TDR8 _cutr.bit._TDR8
#define CUTR_TDR9 _cutr.bit._TDR9
#define CUTR_TDR10 _cutr.bit._TDR10
#define CUTR_TDR11 _cutr.bit._TDR11
#define CUTR_TDR12 _cutr.bit._TDR12
#define CUTR_TDR13 _cutr.bit._TDR13
#define CUTR_TDR14 _cutr.bit._TDR14
#define CUTR_TDR15 _cutr.bit._TDR15
#define CUTR_TDR16 _cutr.bit._TDR16
#define CUTR_TDR17 _cutr.bit._TDR17
#define CUTR_TDR18 _cutr.bit._TDR18
#define CUTR_TDR19 _cutr.bit._TDR19
#define CUTR_TDR20 _cutr.bit._TDR20
#define CUTR_TDR21 _cutr.bit._TDR21
#define CUTR_TDR22 _cutr.bit._TDR22
#define CUTR_TDR23 _cutr.bit._TDR23
__IO_EXTENDED CUTR2STR _cutr2;  
#define CUTR2 _cutr2.word
#define CUTR2_TDR0 _cutr2.bit._TDR0
#define CUTR2_TDR1 _cutr2.bit._TDR1
#define CUTR2_TDR2 _cutr2.bit._TDR2
#define CUTR2_TDR3 _cutr2.bit._TDR3
#define CUTR2_TDR4 _cutr2.bit._TDR4
#define CUTR2_TDR5 _cutr2.bit._TDR5
#define CUTR2_TDR6 _cutr2.bit._TDR6
#define CUTR2_TDR7 _cutr2.bit._TDR7
#define CUTR2_TDR8 _cutr2.bit._TDR8
#define CUTR2_TDR9 _cutr2.bit._TDR9
#define CUTR2_TDR10 _cutr2.bit._TDR10
#define CUTR2_TDR11 _cutr2.bit._TDR11
#define CUTR2_TDR12 _cutr2.bit._TDR12
#define CUTR2_TDR13 _cutr2.bit._TDR13
#define CUTR2_TDR14 _cutr2.bit._TDR14
#define CUTR2_TDR15 _cutr2.bit._TDR15
__IO_EXTENDED CUTR2LSTR _cutr2l;  
#define CUTR2L _cutr2l.byte
#define CUTR2L_TDR0 _cutr2l.bit._TDR0
#define CUTR2L_TDR1 _cutr2l.bit._TDR1
#define CUTR2L_TDR2 _cutr2l.bit._TDR2
#define CUTR2L_TDR3 _cutr2l.bit._TDR3
#define CUTR2L_TDR4 _cutr2l.bit._TDR4
#define CUTR2L_TDR5 _cutr2l.bit._TDR5
#define CUTR2L_TDR6 _cutr2l.bit._TDR6
#define CUTR2L_TDR7 _cutr2l.bit._TDR7
__IO_EXTENDED CUTR2HSTR _cutr2h;  
#define CUTR2H _cutr2h.byte
#define CUTR2H_TDR8 _cutr2h.bit._TDR8
#define CUTR2H_TDR9 _cutr2h.bit._TDR9
#define CUTR2H_TDR10 _cutr2h.bit._TDR10
#define CUTR2H_TDR11 _cutr2h.bit._TDR11
#define CUTR2H_TDR12 _cutr2h.bit._TDR12
#define CUTR2H_TDR13 _cutr2h.bit._TDR13
#define CUTR2H_TDR14 _cutr2h.bit._TDR14
#define CUTR2H_TDR15 _cutr2h.bit._TDR15
__IO_EXTENDED CUTR1STR _cutr1;  
#define CUTR1 _cutr1.word
#define CUTR1_TDR16 _cutr1.bit._TDR16
#define CUTR1_TDR17 _cutr1.bit._TDR17
#define CUTR1_TDR18 _cutr1.bit._TDR18
#define CUTR1_TDR19 _cutr1.bit._TDR19
#define CUTR1_TDR20 _cutr1.bit._TDR20
#define CUTR1_TDR21 _cutr1.bit._TDR21
#define CUTR1_TDR22 _cutr1.bit._TDR22
#define CUTR1_TDR23 _cutr1.bit._TDR23
__IO_EXTENDED CUTR1LSTR _cutr1l;  
#define CUTR1L _cutr1l.byte
#define CUTR1L_TDR16 _cutr1l.bit._TDR16
#define CUTR1L_TDR17 _cutr1l.bit._TDR17
#define CUTR1L_TDR18 _cutr1l.bit._TDR18
#define CUTR1L_TDR19 _cutr1l.bit._TDR19
#define CUTR1L_TDR20 _cutr1l.bit._TDR20
#define CUTR1L_TDR21 _cutr1l.bit._TDR21
#define CUTR1L_TDR22 _cutr1l.bit._TDR22
#define CUTR1L_TDR23 _cutr1l.bit._TDR23
__IO_EXTENDED CUTR1HSTR _cutr1h;  
#define CUTR1H _cutr1h.byte
__IO_EXTENDED TMISRSTR _tmisr;  
#define TMISR _tmisr.byte
#define TMISR_TMIS0 _tmisr.bit._TMIS0
#define TMISR_TMIS1 _tmisr.bit._TMIS1
#define TMISR_TMIS2 _tmisr.bit._TMIS2
#define TMISR_TMIS3 _tmisr.bit._TMIS3
#define TMISR_TMIS4 _tmisr.bit._TMIS4
#define TMISR_TMIS5 _tmisr.bit._TMIS5
__IO_EXTENDED SMR7STR _smr7;  
#define SMR7 _smr7.byte
#define SMR7_SOE _smr7.bit._SOE
#define SMR7_SCKE _smr7.bit._SCKE
#define SMR7_UPCL _smr7.bit._UPCL
#define SMR7_REST _smr7.bit._REST
#define SMR7_EXT _smr7.bit._EXT
#define SMR7_OTO _smr7.bit._OTO
#define SMR7_MD0 _smr7.bit._MD0
#define SMR7_MD1 _smr7.bit._MD1
#define SMR7_MD _smr7.bitc._MD
__IO_EXTENDED SCR7STR _scr7;  
#define SCR7 _scr7.byte
#define SCR7_TXE _scr7.bit._TXE
#define SCR7_RXE _scr7.bit._RXE
#define SCR7_CRE _scr7.bit._CRE
#define SCR7_AD _scr7.bit._AD
#define SCR7_CL _scr7.bit._CL
#define SCR7_SBL _scr7.bit._SBL
#define SCR7_P _scr7.bit._P
#define SCR7_PEN _scr7.bit._PEN
__IO_EXTENDED IO_BYTE _tdr7;
#define TDR7 _tdr7   
__IO_EXTENDED IO_BYTE _rdr7;
#define RDR7 _rdr7   
__IO_EXTENDED SSR7STR _ssr7;  
#define SSR7 _ssr7.byte
#define SSR7_TIE _ssr7.bit._TIE
#define SSR7_RIE _ssr7.bit._RIE
#define SSR7_BDS _ssr7.bit._BDS
#define SSR7_TDRE _ssr7.bit._TDRE
#define SSR7_RDRF _ssr7.bit._RDRF
#define SSR7_FRE _ssr7.bit._FRE
#define SSR7_ORE _ssr7.bit._ORE
#define SSR7_PE _ssr7.bit._PE
__IO_EXTENDED ECCR7STR _eccr7;  
#define ECCR7 _eccr7.byte
#define ECCR7_TBI _eccr7.bit._TBI
#define ECCR7_RBI _eccr7.bit._RBI
#define ECCR7_BIE _eccr7.bit._BIE
#define ECCR7_SSM _eccr7.bit._SSM
#define ECCR7_SCDE _eccr7.bit._SCDE
#define ECCR7_MS _eccr7.bit._MS
#define ECCR7_LBR _eccr7.bit._LBR
#define ECCR7_INV _eccr7.bit._INV
__IO_EXTENDED ESCR7STR _escr7;  
#define ESCR7 _escr7.byte
#define ESCR7_SCES _escr7.bit._SCES
#define ESCR7_CCO _escr7.bit._CCO
#define ESCR7_SIOP _escr7.bit._SIOP
#define ESCR7_SOPE _escr7.bit._SOPE
#define ESCR7_LBL0 _escr7.bit._LBL0
#define ESCR7_LBL1 _escr7.bit._LBL1
#define ESCR7_LBD _escr7.bit._LBD
#define ESCR7_LBIE _escr7.bit._LBIE
#define ESCR7_LBL _escr7.bitc._LBL
__IO_EXTENDED BGR7STR _bgr7;  
#define BGR7 _bgr7.word
#define BGR7_BGR0 _bgr7.bit._BGR0
#define BGR7_BGR1 _bgr7.bit._BGR1
#define BGR7_BGR2 _bgr7.bit._BGR2
#define BGR7_BGR3 _bgr7.bit._BGR3
#define BGR7_BGR4 _bgr7.bit._BGR4
#define BGR7_BGR5 _bgr7.bit._BGR5
#define BGR7_BGR6 _bgr7.bit._BGR6
#define BGR7_BGR7 _bgr7.bit._BGR7
#define BGR7_BGR8 _bgr7.bit._BGR8
#define BGR7_BGR9 _bgr7.bit._BGR9
#define BGR7_BGR10 _bgr7.bit._BGR10
#define BGR7_BGR11 _bgr7.bit._BGR11
#define BGR7_BGR12 _bgr7.bit._BGR12
#define BGR7_BGR13 _bgr7.bit._BGR13
#define BGR7_BGR14 _bgr7.bit._BGR14
#define BGR7_BGR15 _bgr7.bit._BGR15
#define BGR7_BGR _bgr7.bitc._BGR
__IO_EXTENDED BGRL7STR _bgrl7;  
#define BGRL7 _bgrl7.byte
#define BGRL7_BGR0 _bgrl7.bit._BGR0
#define BGRL7_BGR1 _bgrl7.bit._BGR1
#define BGRL7_BGR2 _bgrl7.bit._BGR2
#define BGRL7_BGR3 _bgrl7.bit._BGR3
#define BGRL7_BGR4 _bgrl7.bit._BGR4
#define BGRL7_BGR5 _bgrl7.bit._BGR5
#define BGRL7_BGR6 _bgrl7.bit._BGR6
#define BGRL7_BGR7 _bgrl7.bit._BGR7
__IO_EXTENDED BGRH7STR _bgrh7;  
#define BGRH7 _bgrh7.byte
#define BGRH7_BGR8 _bgrh7.bit._BGR8
#define BGRH7_BGR9 _bgrh7.bit._BGR9
#define BGRH7_BGR10 _bgrh7.bit._BGR10
#define BGRH7_BGR11 _bgrh7.bit._BGR11
#define BGRH7_BGR12 _bgrh7.bit._BGR12
#define BGRH7_BGR13 _bgrh7.bit._BGR13
#define BGRH7_BGR14 _bgrh7.bit._BGR14
#define BGRH7_BGR15 _bgrh7.bit._BGR15
__IO_EXTENDED ESIR7STR _esir7;  
#define ESIR7 _esir7.byte
#define ESIR7_AICD _esir7.bit._AICD
#define ESIR7_RBI _esir7.bit._RBI
#define ESIR7_RDRF _esir7.bit._RDRF
#define ESIR7_TDRE _esir7.bit._TDRE
__IO_EXTENDED SMR8STR _smr8;  
#define SMR8 _smr8.byte
#define SMR8_SOE _smr8.bit._SOE
#define SMR8_SCKE _smr8.bit._SCKE
#define SMR8_UPCL _smr8.bit._UPCL
#define SMR8_REST _smr8.bit._REST
#define SMR8_EXT _smr8.bit._EXT
#define SMR8_OTO _smr8.bit._OTO
#define SMR8_MD0 _smr8.bit._MD0
#define SMR8_MD1 _smr8.bit._MD1
#define SMR8_MD _smr8.bitc._MD
__IO_EXTENDED SCR8STR _scr8;  
#define SCR8 _scr8.byte
#define SCR8_TXE _scr8.bit._TXE
#define SCR8_RXE _scr8.bit._RXE
#define SCR8_CRE _scr8.bit._CRE
#define SCR8_AD _scr8.bit._AD
#define SCR8_CL _scr8.bit._CL
#define SCR8_SBL _scr8.bit._SBL
#define SCR8_P _scr8.bit._P
#define SCR8_PEN _scr8.bit._PEN
__IO_EXTENDED IO_BYTE _tdr8;
#define TDR8 _tdr8   
__IO_EXTENDED IO_BYTE _rdr8;
#define RDR8 _rdr8   
__IO_EXTENDED SSR8STR _ssr8;  
#define SSR8 _ssr8.byte
#define SSR8_TIE _ssr8.bit._TIE
#define SSR8_RIE _ssr8.bit._RIE
#define SSR8_BDS _ssr8.bit._BDS
#define SSR8_TDRE _ssr8.bit._TDRE
#define SSR8_RDRF _ssr8.bit._RDRF
#define SSR8_FRE _ssr8.bit._FRE
#define SSR8_ORE _ssr8.bit._ORE
#define SSR8_PE _ssr8.bit._PE
__IO_EXTENDED ECCR8STR _eccr8;  
#define ECCR8 _eccr8.byte
#define ECCR8_TBI _eccr8.bit._TBI
#define ECCR8_RBI _eccr8.bit._RBI
#define ECCR8_BIE _eccr8.bit._BIE
#define ECCR8_SSM _eccr8.bit._SSM
#define ECCR8_SCDE _eccr8.bit._SCDE
#define ECCR8_MS _eccr8.bit._MS
#define ECCR8_LBR _eccr8.bit._LBR
#define ECCR8_INV _eccr8.bit._INV
__IO_EXTENDED ESCR8STR _escr8;  
#define ESCR8 _escr8.byte
#define ESCR8_SCES _escr8.bit._SCES
#define ESCR8_CCO _escr8.bit._CCO
#define ESCR8_SIOP _escr8.bit._SIOP
#define ESCR8_SOPE _escr8.bit._SOPE
#define ESCR8_LBL0 _escr8.bit._LBL0
#define ESCR8_LBL1 _escr8.bit._LBL1
#define ESCR8_LBD _escr8.bit._LBD
#define ESCR8_LBIE _escr8.bit._LBIE
#define ESCR8_LBL _escr8.bitc._LBL
__IO_EXTENDED BGR8STR _bgr8;  
#define BGR8 _bgr8.word
#define BGR8_BGR0 _bgr8.bit._BGR0
#define BGR8_BGR1 _bgr8.bit._BGR1
#define BGR8_BGR2 _bgr8.bit._BGR2
#define BGR8_BGR3 _bgr8.bit._BGR3
#define BGR8_BGR4 _bgr8.bit._BGR4
#define BGR8_BGR5 _bgr8.bit._BGR5
#define BGR8_BGR6 _bgr8.bit._BGR6
#define BGR8_BGR7 _bgr8.bit._BGR7
#define BGR8_BGR8 _bgr8.bit._BGR8
#define BGR8_BGR9 _bgr8.bit._BGR9
#define BGR8_BGR10 _bgr8.bit._BGR10
#define BGR8_BGR11 _bgr8.bit._BGR11
#define BGR8_BGR12 _bgr8.bit._BGR12
#define BGR8_BGR13 _bgr8.bit._BGR13
#define BGR8_BGR14 _bgr8.bit._BGR14
#define BGR8_BGR15 _bgr8.bit._BGR15
#define BGR8_BGR _bgr8.bitc._BGR
__IO_EXTENDED BGRL8STR _bgrl8;  
#define BGRL8 _bgrl8.byte
#define BGRL8_BGR0 _bgrl8.bit._BGR0
#define BGRL8_BGR1 _bgrl8.bit._BGR1
#define BGRL8_BGR2 _bgrl8.bit._BGR2
#define BGRL8_BGR3 _bgrl8.bit._BGR3
#define BGRL8_BGR4 _bgrl8.bit._BGR4
#define BGRL8_BGR5 _bgrl8.bit._BGR5
#define BGRL8_BGR6 _bgrl8.bit._BGR6
#define BGRL8_BGR7 _bgrl8.bit._BGR7
__IO_EXTENDED BGRH8STR _bgrh8;  
#define BGRH8 _bgrh8.byte
#define BGRH8_BGR8 _bgrh8.bit._BGR8
#define BGRH8_BGR9 _bgrh8.bit._BGR9
#define BGRH8_BGR10 _bgrh8.bit._BGR10
#define BGRH8_BGR11 _bgrh8.bit._BGR11
#define BGRH8_BGR12 _bgrh8.bit._BGR12
#define BGRH8_BGR13 _bgrh8.bit._BGR13
#define BGRH8_BGR14 _bgrh8.bit._BGR14
#define BGRH8_BGR15 _bgrh8.bit._BGR15
__IO_EXTENDED ESIR8STR _esir8;  
#define ESIR8 _esir8.byte
#define ESIR8_AICD _esir8.bit._AICD
#define ESIR8_RBI _esir8.bit._RBI
#define ESIR8_RDRF _esir8.bit._RDRF
#define ESIR8_TDRE _esir8.bit._TDRE
__IO_EXTENDED SMR9STR _smr9;  
#define SMR9 _smr9.byte
#define SMR9_SOE _smr9.bit._SOE
#define SMR9_SCKE _smr9.bit._SCKE
#define SMR9_UPCL _smr9.bit._UPCL
#define SMR9_REST _smr9.bit._REST
#define SMR9_EXT _smr9.bit._EXT
#define SMR9_OTO _smr9.bit._OTO
#define SMR9_MD0 _smr9.bit._MD0
#define SMR9_MD1 _smr9.bit._MD1
#define SMR9_MD _smr9.bitc._MD
__IO_EXTENDED SCR9STR _scr9;  
#define SCR9 _scr9.byte
#define SCR9_TXE _scr9.bit._TXE
#define SCR9_RXE _scr9.bit._RXE
#define SCR9_CRE _scr9.bit._CRE
#define SCR9_AD _scr9.bit._AD
#define SCR9_CL _scr9.bit._CL
#define SCR9_SBL _scr9.bit._SBL
#define SCR9_P _scr9.bit._P
#define SCR9_PEN _scr9.bit._PEN
__IO_EXTENDED IO_BYTE _tdr9;
#define TDR9 _tdr9   
__IO_EXTENDED IO_BYTE _rdr9;
#define RDR9 _rdr9   
__IO_EXTENDED SSR9STR _ssr9;  
#define SSR9 _ssr9.byte
#define SSR9_TIE _ssr9.bit._TIE
#define SSR9_RIE _ssr9.bit._RIE
#define SSR9_BDS _ssr9.bit._BDS
#define SSR9_TDRE _ssr9.bit._TDRE
#define SSR9_RDRF _ssr9.bit._RDRF
#define SSR9_FRE _ssr9.bit._FRE
#define SSR9_ORE _ssr9.bit._ORE
#define SSR9_PE _ssr9.bit._PE
__IO_EXTENDED ECCR9STR _eccr9;  
#define ECCR9 _eccr9.byte
#define ECCR9_TBI _eccr9.bit._TBI
#define ECCR9_RBI _eccr9.bit._RBI
#define ECCR9_BIE _eccr9.bit._BIE
#define ECCR9_SSM _eccr9.bit._SSM
#define ECCR9_SCDE _eccr9.bit._SCDE
#define ECCR9_MS _eccr9.bit._MS
#define ECCR9_LBR _eccr9.bit._LBR
#define ECCR9_INV _eccr9.bit._INV
__IO_EXTENDED ESCR9STR _escr9;  
#define ESCR9 _escr9.byte
#define ESCR9_SCES _escr9.bit._SCES
#define ESCR9_CCO _escr9.bit._CCO
#define ESCR9_SIOP _escr9.bit._SIOP
#define ESCR9_SOPE _escr9.bit._SOPE
#define ESCR9_LBL0 _escr9.bit._LBL0
#define ESCR9_LBL1 _escr9.bit._LBL1
#define ESCR9_LBD _escr9.bit._LBD
#define ESCR9_LBIE _escr9.bit._LBIE
#define ESCR9_LBL _escr9.bitc._LBL
__IO_EXTENDED BGR9STR _bgr9;  
#define BGR9 _bgr9.word
#define BGR9_BGR0 _bgr9.bit._BGR0
#define BGR9_BGR1 _bgr9.bit._BGR1
#define BGR9_BGR2 _bgr9.bit._BGR2
#define BGR9_BGR3 _bgr9.bit._BGR3
#define BGR9_BGR4 _bgr9.bit._BGR4
#define BGR9_BGR5 _bgr9.bit._BGR5
#define BGR9_BGR6 _bgr9.bit._BGR6
#define BGR9_BGR7 _bgr9.bit._BGR7
#define BGR9_BGR8 _bgr9.bit._BGR8
#define BGR9_BGR9 _bgr9.bit._BGR9
#define BGR9_BGR10 _bgr9.bit._BGR10
#define BGR9_BGR11 _bgr9.bit._BGR11
#define BGR9_BGR12 _bgr9.bit._BGR12
#define BGR9_BGR13 _bgr9.bit._BGR13
#define BGR9_BGR14 _bgr9.bit._BGR14
#define BGR9_BGR15 _bgr9.bit._BGR15
#define BGR9_BGR _bgr9.bitc._BGR
__IO_EXTENDED BGRL9STR _bgrl9;  
#define BGRL9 _bgrl9.byte
#define BGRL9_BGR0 _bgrl9.bit._BGR0
#define BGRL9_BGR1 _bgrl9.bit._BGR1
#define BGRL9_BGR2 _bgrl9.bit._BGR2
#define BGRL9_BGR3 _bgrl9.bit._BGR3
#define BGRL9_BGR4 _bgrl9.bit._BGR4
#define BGRL9_BGR5 _bgrl9.bit._BGR5
#define BGRL9_BGR6 _bgrl9.bit._BGR6
#define BGRL9_BGR7 _bgrl9.bit._BGR7
__IO_EXTENDED BGRH9STR _bgrh9;  
#define BGRH9 _bgrh9.byte
#define BGRH9_BGR8 _bgrh9.bit._BGR8
#define BGRH9_BGR9 _bgrh9.bit._BGR9
#define BGRH9_BGR10 _bgrh9.bit._BGR10
#define BGRH9_BGR11 _bgrh9.bit._BGR11
#define BGRH9_BGR12 _bgrh9.bit._BGR12
#define BGRH9_BGR13 _bgrh9.bit._BGR13
#define BGRH9_BGR14 _bgrh9.bit._BGR14
#define BGRH9_BGR15 _bgrh9.bit._BGR15
__IO_EXTENDED ESIR9STR _esir9;  
#define ESIR9 _esir9.byte
#define ESIR9_AICD _esir9.bit._AICD
#define ESIR9_RBI _esir9.bit._RBI
#define ESIR9_RDRF _esir9.bit._RDRF
#define ESIR9_TDRE _esir9.bit._TDRE
__IO_EXTENDED ACSR0STR _acsr0;  
#define ACSR0 _acsr0.byte
#define ACSR0_PD _acsr0.bit._PD
#define ACSR0_IEN _acsr0.bit._IEN
#define ACSR0_IRQ _acsr0.bit._IRQ
#define ACSR0_OUT1 _acsr0.bit._OUT1
#define ACSR0_OUT2 _acsr0.bit._OUT2
#define ACSR0_UVEN _acsr0.bit._UVEN
#define ACSR0_OVEN _acsr0.bit._OVEN
#define ACSR0_CMD _acsr0.bit._CMD
__IO_EXTENDED AECSR0STR _aecsr0;  
#define AECSR0 _aecsr0.byte
#define AECSR0_INTREF _aecsr0.bit._INTREF
#define AECSR0_ACE _aecsr0.bit._ACE
__IO_EXTENDED ACSR1STR _acsr1;  
#define ACSR1 _acsr1.byte
#define ACSR1_PD _acsr1.bit._PD
#define ACSR1_IEN _acsr1.bit._IEN
#define ACSR1_IRQ _acsr1.bit._IRQ
#define ACSR1_OUT1 _acsr1.bit._OUT1
#define ACSR1_OUT2 _acsr1.bit._OUT2
#define ACSR1_UVEN _acsr1.bit._UVEN
#define ACSR1_OVEN _acsr1.bit._OVEN
#define ACSR1_CMD _acsr1.bit._CMD
__IO_EXTENDED AECSR1STR _aecsr1;  
#define AECSR1 _aecsr1.byte
#define AECSR1_INTREF _aecsr1.bit._INTREF
#define AECSR1_ACE _aecsr1.bit._ACE
__IO_EXTENDED PTMR6STR _ptmr6;  
#define PTMR6 _ptmr6.word
#define PTMR6_D0 _ptmr6.bit._D0
#define PTMR6_D1 _ptmr6.bit._D1
#define PTMR6_D2 _ptmr6.bit._D2
#define PTMR6_D3 _ptmr6.bit._D3
#define PTMR6_D4 _ptmr6.bit._D4
#define PTMR6_D5 _ptmr6.bit._D5
#define PTMR6_D6 _ptmr6.bit._D6
#define PTMR6_D7 _ptmr6.bit._D7
#define PTMR6_D8 _ptmr6.bit._D8
#define PTMR6_D9 _ptmr6.bit._D9
#define PTMR6_D10 _ptmr6.bit._D10
#define PTMR6_D11 _ptmr6.bit._D11
#define PTMR6_D12 _ptmr6.bit._D12
#define PTMR6_D13 _ptmr6.bit._D13
#define PTMR6_D14 _ptmr6.bit._D14
#define PTMR6_D15 _ptmr6.bit._D15
#define PTMR6_D _ptmr6.bitc._D
__IO_EXTENDED PCSR6STR _pcsr6;  
#define PCSR6 _pcsr6.word
#define PCSR6_D0 _pcsr6.bit._D0
#define PCSR6_D1 _pcsr6.bit._D1
#define PCSR6_D2 _pcsr6.bit._D2
#define PCSR6_D3 _pcsr6.bit._D3
#define PCSR6_D4 _pcsr6.bit._D4
#define PCSR6_D5 _pcsr6.bit._D5
#define PCSR6_D6 _pcsr6.bit._D6
#define PCSR6_D7 _pcsr6.bit._D7
#define PCSR6_D8 _pcsr6.bit._D8
#define PCSR6_D9 _pcsr6.bit._D9
#define PCSR6_D10 _pcsr6.bit._D10
#define PCSR6_D11 _pcsr6.bit._D11
#define PCSR6_D12 _pcsr6.bit._D12
#define PCSR6_D13 _pcsr6.bit._D13
#define PCSR6_D14 _pcsr6.bit._D14
#define PCSR6_D15 _pcsr6.bit._D15
#define PCSR6_D _pcsr6.bitc._D
__IO_EXTENDED PDUT6STR _pdut6;  
#define PDUT6 _pdut6.word
#define PDUT6_D0 _pdut6.bit._D0
#define PDUT6_D1 _pdut6.bit._D1
#define PDUT6_D2 _pdut6.bit._D2
#define PDUT6_D3 _pdut6.bit._D3
#define PDUT6_D4 _pdut6.bit._D4
#define PDUT6_D5 _pdut6.bit._D5
#define PDUT6_D6 _pdut6.bit._D6
#define PDUT6_D7 _pdut6.bit._D7
#define PDUT6_D8 _pdut6.bit._D8
#define PDUT6_D9 _pdut6.bit._D9
#define PDUT6_D10 _pdut6.bit._D10
#define PDUT6_D11 _pdut6.bit._D11
#define PDUT6_D12 _pdut6.bit._D12
#define PDUT6_D13 _pdut6.bit._D13
#define PDUT6_D14 _pdut6.bit._D14
#define PDUT6_D15 _pdut6.bit._D15
#define PDUT6_D _pdut6.bitc._D
__IO_EXTENDED PCN6STR _pcn6;  
#define PCN6 _pcn6.word
#define PCN6_OSEL _pcn6.bit._OSEL
#define PCN6_OE _pcn6.bit._OE
#define PCN6_IRS0 _pcn6.bit._IRS0
#define PCN6_IRS1 _pcn6.bit._IRS1
#define PCN6_IRQF _pcn6.bit._IRQF
#define PCN6_IREN _pcn6.bit._IREN
#define PCN6_EGS0 _pcn6.bit._EGS0
#define PCN6_EGS1 _pcn6.bit._EGS1
#define PCN6_PGMS _pcn6.bit._PGMS
#define PCN6_CKS0 _pcn6.bit._CKS0
#define PCN6_CKS1 _pcn6.bit._CKS1
#define PCN6_RTRG _pcn6.bit._RTRG
#define PCN6_MDSE _pcn6.bit._MDSE
#define PCN6_STGR _pcn6.bit._STGR
#define PCN6_CNTE _pcn6.bit._CNTE
#define PCN6_IRS _pcn6.bitc._IRS
#define PCN6_EGS _pcn6.bitc._EGS
#define PCN6_CKS _pcn6.bitc._CKS
__IO_EXTENDED PCNL6STR _pcnl6;  
#define PCNL6 _pcnl6.byte
#define PCNL6_OSEL _pcnl6.bit._OSEL
#define PCNL6_OE _pcnl6.bit._OE
#define PCNL6_IRS0 _pcnl6.bit._IRS0
#define PCNL6_IRS1 _pcnl6.bit._IRS1
#define PCNL6_IRQF _pcnl6.bit._IRQF
#define PCNL6_IREN _pcnl6.bit._IREN
#define PCNL6_EGS0 _pcnl6.bit._EGS0
#define PCNL6_EGS1 _pcnl6.bit._EGS1
#define PCNL6_IRS _pcnl6.bitc._IRS
#define PCNL6_EGS _pcnl6.bitc._EGS
__IO_EXTENDED PCNH6STR _pcnh6;  
#define PCNH6 _pcnh6.byte
#define PCNH6_PGMS _pcnh6.bit._PGMS
#define PCNH6_CKS0 _pcnh6.bit._CKS0
#define PCNH6_CKS1 _pcnh6.bit._CKS1
#define PCNH6_RTRG _pcnh6.bit._RTRG
#define PCNH6_MDSE _pcnh6.bit._MDSE
#define PCNH6_STGR _pcnh6.bit._STGR
#define PCNH6_CNTE _pcnh6.bit._CNTE
#define PCNH6_CKS _pcnh6.bitc._CKS
__IO_EXTENDED PTMR7STR _ptmr7;  
#define PTMR7 _ptmr7.word
#define PTMR7_D0 _ptmr7.bit._D0
#define PTMR7_D1 _ptmr7.bit._D1
#define PTMR7_D2 _ptmr7.bit._D2
#define PTMR7_D3 _ptmr7.bit._D3
#define PTMR7_D4 _ptmr7.bit._D4
#define PTMR7_D5 _ptmr7.bit._D5
#define PTMR7_D6 _ptmr7.bit._D6
#define PTMR7_D7 _ptmr7.bit._D7
#define PTMR7_D8 _ptmr7.bit._D8
#define PTMR7_D9 _ptmr7.bit._D9
#define PTMR7_D10 _ptmr7.bit._D10
#define PTMR7_D11 _ptmr7.bit._D11
#define PTMR7_D12 _ptmr7.bit._D12
#define PTMR7_D13 _ptmr7.bit._D13
#define PTMR7_D14 _ptmr7.bit._D14
#define PTMR7_D15 _ptmr7.bit._D15
#define PTMR7_D _ptmr7.bitc._D
__IO_EXTENDED PCSR7STR _pcsr7;  
#define PCSR7 _pcsr7.word
#define PCSR7_D0 _pcsr7.bit._D0
#define PCSR7_D1 _pcsr7.bit._D1
#define PCSR7_D2 _pcsr7.bit._D2
#define PCSR7_D3 _pcsr7.bit._D3
#define PCSR7_D4 _pcsr7.bit._D4
#define PCSR7_D5 _pcsr7.bit._D5
#define PCSR7_D6 _pcsr7.bit._D6
#define PCSR7_D7 _pcsr7.bit._D7
#define PCSR7_D8 _pcsr7.bit._D8
#define PCSR7_D9 _pcsr7.bit._D9
#define PCSR7_D10 _pcsr7.bit._D10
#define PCSR7_D11 _pcsr7.bit._D11
#define PCSR7_D12 _pcsr7.bit._D12
#define PCSR7_D13 _pcsr7.bit._D13
#define PCSR7_D14 _pcsr7.bit._D14
#define PCSR7_D15 _pcsr7.bit._D15
#define PCSR7_D _pcsr7.bitc._D
__IO_EXTENDED PDUT7STR _pdut7;  
#define PDUT7 _pdut7.word
#define PDUT7_D0 _pdut7.bit._D0
#define PDUT7_D1 _pdut7.bit._D1
#define PDUT7_D2 _pdut7.bit._D2
#define PDUT7_D3 _pdut7.bit._D3
#define PDUT7_D4 _pdut7.bit._D4
#define PDUT7_D5 _pdut7.bit._D5
#define PDUT7_D6 _pdut7.bit._D6
#define PDUT7_D7 _pdut7.bit._D7
#define PDUT7_D8 _pdut7.bit._D8
#define PDUT7_D9 _pdut7.bit._D9
#define PDUT7_D10 _pdut7.bit._D10
#define PDUT7_D11 _pdut7.bit._D11
#define PDUT7_D12 _pdut7.bit._D12
#define PDUT7_D13 _pdut7.bit._D13
#define PDUT7_D14 _pdut7.bit._D14
#define PDUT7_D15 _pdut7.bit._D15
#define PDUT7_D _pdut7.bitc._D
__IO_EXTENDED PCN7STR _pcn7;  
#define PCN7 _pcn7.word
#define PCN7_OSEL _pcn7.bit._OSEL
#define PCN7_OE _pcn7.bit._OE
#define PCN7_IRS0 _pcn7.bit._IRS0
#define PCN7_IRS1 _pcn7.bit._IRS1
#define PCN7_IRQF _pcn7.bit._IRQF
#define PCN7_IREN _pcn7.bit._IREN
#define PCN7_EGS0 _pcn7.bit._EGS0
#define PCN7_EGS1 _pcn7.bit._EGS1
#define PCN7_PGMS _pcn7.bit._PGMS
#define PCN7_CKS0 _pcn7.bit._CKS0
#define PCN7_CKS1 _pcn7.bit._CKS1
#define PCN7_RTRG _pcn7.bit._RTRG
#define PCN7_MDSE _pcn7.bit._MDSE
#define PCN7_STGR _pcn7.bit._STGR
#define PCN7_CNTE _pcn7.bit._CNTE
#define PCN7_IRS _pcn7.bitc._IRS
#define PCN7_EGS _pcn7.bitc._EGS
#define PCN7_CKS _pcn7.bitc._CKS
__IO_EXTENDED PCNL7STR _pcnl7;  
#define PCNL7 _pcnl7.byte
#define PCNL7_OSEL _pcnl7.bit._OSEL
#define PCNL7_OE _pcnl7.bit._OE
#define PCNL7_IRS0 _pcnl7.bit._IRS0
#define PCNL7_IRS1 _pcnl7.bit._IRS1
#define PCNL7_IRQF _pcnl7.bit._IRQF
#define PCNL7_IREN _pcnl7.bit._IREN
#define PCNL7_EGS0 _pcnl7.bit._EGS0
#define PCNL7_EGS1 _pcnl7.bit._EGS1
#define PCNL7_IRS _pcnl7.bitc._IRS
#define PCNL7_EGS _pcnl7.bitc._EGS
__IO_EXTENDED PCNH7STR _pcnh7;  
#define PCNH7 _pcnh7.byte
#define PCNH7_PGMS _pcnh7.bit._PGMS
#define PCNH7_CKS0 _pcnh7.bit._CKS0
#define PCNH7_CKS1 _pcnh7.bit._CKS1
#define PCNH7_RTRG _pcnh7.bit._RTRG
#define PCNH7_MDSE _pcnh7.bit._MDSE
#define PCNH7_STGR _pcnh7.bit._STGR
#define PCNH7_CNTE _pcnh7.bit._CNTE
#define PCNH7_CKS _pcnh7.bitc._CKS
__IO_EXTENDED GCN12STR _gcn12;  
#define GCN12 _gcn12.word
#define GCN12_TSEL00 _gcn12.bit._TSEL00
#define GCN12_TSEL01 _gcn12.bit._TSEL01
#define GCN12_TSEL02 _gcn12.bit._TSEL02
#define GCN12_TSEL03 _gcn12.bit._TSEL03
#define GCN12_TSEL10 _gcn12.bit._TSEL10
#define GCN12_TSEL11 _gcn12.bit._TSEL11
#define GCN12_TSEL12 _gcn12.bit._TSEL12
#define GCN12_TSEL13 _gcn12.bit._TSEL13
#define GCN12_TSEL20 _gcn12.bit._TSEL20
#define GCN12_TSEL21 _gcn12.bit._TSEL21
#define GCN12_TSEL22 _gcn12.bit._TSEL22
#define GCN12_TSEL23 _gcn12.bit._TSEL23
#define GCN12_TSEL30 _gcn12.bit._TSEL30
#define GCN12_TSEL31 _gcn12.bit._TSEL31
#define GCN12_TSEL32 _gcn12.bit._TSEL32
#define GCN12_TSEL33 _gcn12.bit._TSEL33
#define GCN12_TSEL0 _gcn12.bitc._TSEL0
#define GCN12_TSEL1 _gcn12.bitc._TSEL1
#define GCN12_TSEL2 _gcn12.bitc._TSEL2
#define GCN12_TSEL3 _gcn12.bitc._TSEL3
__IO_EXTENDED GCN1L2STR _gcn1l2;  
#define GCN1L2 _gcn1l2.byte
#define GCN1L2_TSEL00 _gcn1l2.bit._TSEL00
#define GCN1L2_TSEL01 _gcn1l2.bit._TSEL01
#define GCN1L2_TSEL02 _gcn1l2.bit._TSEL02
#define GCN1L2_TSEL03 _gcn1l2.bit._TSEL03
#define GCN1L2_TSEL10 _gcn1l2.bit._TSEL10
#define GCN1L2_TSEL11 _gcn1l2.bit._TSEL11
#define GCN1L2_TSEL12 _gcn1l2.bit._TSEL12
#define GCN1L2_TSEL13 _gcn1l2.bit._TSEL13
#define GCN1L2_TSEL0 _gcn1l2.bitc._TSEL0
#define GCN1L2_TSEL1 _gcn1l2.bitc._TSEL1
__IO_EXTENDED GCN1H2STR _gcn1h2;  
#define GCN1H2 _gcn1h2.byte
#define GCN1H2_TSEL20 _gcn1h2.bit._TSEL20
#define GCN1H2_TSEL21 _gcn1h2.bit._TSEL21
#define GCN1H2_TSEL22 _gcn1h2.bit._TSEL22
#define GCN1H2_TSEL23 _gcn1h2.bit._TSEL23
#define GCN1H2_TSEL30 _gcn1h2.bit._TSEL30
#define GCN1H2_TSEL31 _gcn1h2.bit._TSEL31
#define GCN1H2_TSEL32 _gcn1h2.bit._TSEL32
#define GCN1H2_TSEL33 _gcn1h2.bit._TSEL33
#define GCN1H2_TSEL2 _gcn1h2.bitc._TSEL2
#define GCN1H2_TSEL3 _gcn1h2.bitc._TSEL3
__IO_EXTENDED GCN22STR _gcn22;  
#define GCN22 _gcn22.word
#define GCN22_EN0 _gcn22.bit._EN0
#define GCN22_EN1 _gcn22.bit._EN1
#define GCN22_EN2 _gcn22.bit._EN2
#define GCN22_EN3 _gcn22.bit._EN3
#define GCN22_CKSEL0 _gcn22.bit._CKSEL0
#define GCN22_CKSEL1 _gcn22.bit._CKSEL1
#define GCN22_CKSEL2 _gcn22.bit._CKSEL2
#define GCN22_CKSEL3 _gcn22.bit._CKSEL3
#define GCN22_EN _gcn22.bitc._EN
#define GCN22_CKSEL _gcn22.bitc._CKSEL
__IO_EXTENDED GCN2L2STR _gcn2l2;  
#define GCN2L2 _gcn2l2.byte
#define GCN2L2_EN0 _gcn2l2.bit._EN0
#define GCN2L2_EN1 _gcn2l2.bit._EN1
#define GCN2L2_EN2 _gcn2l2.bit._EN2
#define GCN2L2_EN3 _gcn2l2.bit._EN3
#define GCN2L2_EN _gcn2l2.bitc._EN
__IO_EXTENDED GCN2H2STR _gcn2h2;  
#define GCN2H2 _gcn2h2.byte
#define GCN2H2_CKSEL0 _gcn2h2.bit._CKSEL0
#define GCN2H2_CKSEL1 _gcn2h2.bit._CKSEL1
#define GCN2H2_CKSEL2 _gcn2h2.bit._CKSEL2
#define GCN2H2_CKSEL3 _gcn2h2.bit._CKSEL3
#define GCN2H2_CKSEL _gcn2h2.bitc._CKSEL
__IO_EXTENDED PTMR8STR _ptmr8;  
#define PTMR8 _ptmr8.word
#define PTMR8_D0 _ptmr8.bit._D0
#define PTMR8_D1 _ptmr8.bit._D1
#define PTMR8_D2 _ptmr8.bit._D2
#define PTMR8_D3 _ptmr8.bit._D3
#define PTMR8_D4 _ptmr8.bit._D4
#define PTMR8_D5 _ptmr8.bit._D5
#define PTMR8_D6 _ptmr8.bit._D6
#define PTMR8_D7 _ptmr8.bit._D7
#define PTMR8_D8 _ptmr8.bit._D8
#define PTMR8_D9 _ptmr8.bit._D9
#define PTMR8_D10 _ptmr8.bit._D10
#define PTMR8_D11 _ptmr8.bit._D11
#define PTMR8_D12 _ptmr8.bit._D12
#define PTMR8_D13 _ptmr8.bit._D13
#define PTMR8_D14 _ptmr8.bit._D14
#define PTMR8_D15 _ptmr8.bit._D15
#define PTMR8_D _ptmr8.bitc._D
__IO_EXTENDED PCSR8STR _pcsr8;  
#define PCSR8 _pcsr8.word
#define PCSR8_D0 _pcsr8.bit._D0
#define PCSR8_D1 _pcsr8.bit._D1
#define PCSR8_D2 _pcsr8.bit._D2
#define PCSR8_D3 _pcsr8.bit._D3
#define PCSR8_D4 _pcsr8.bit._D4
#define PCSR8_D5 _pcsr8.bit._D5
#define PCSR8_D6 _pcsr8.bit._D6
#define PCSR8_D7 _pcsr8.bit._D7
#define PCSR8_D8 _pcsr8.bit._D8
#define PCSR8_D9 _pcsr8.bit._D9
#define PCSR8_D10 _pcsr8.bit._D10
#define PCSR8_D11 _pcsr8.bit._D11
#define PCSR8_D12 _pcsr8.bit._D12
#define PCSR8_D13 _pcsr8.bit._D13
#define PCSR8_D14 _pcsr8.bit._D14
#define PCSR8_D15 _pcsr8.bit._D15
#define PCSR8_D _pcsr8.bitc._D
__IO_EXTENDED PDUT8STR _pdut8;  
#define PDUT8 _pdut8.word
#define PDUT8_D0 _pdut8.bit._D0
#define PDUT8_D1 _pdut8.bit._D1
#define PDUT8_D2 _pdut8.bit._D2
#define PDUT8_D3 _pdut8.bit._D3
#define PDUT8_D4 _pdut8.bit._D4
#define PDUT8_D5 _pdut8.bit._D5
#define PDUT8_D6 _pdut8.bit._D6
#define PDUT8_D7 _pdut8.bit._D7
#define PDUT8_D8 _pdut8.bit._D8
#define PDUT8_D9 _pdut8.bit._D9
#define PDUT8_D10 _pdut8.bit._D10
#define PDUT8_D11 _pdut8.bit._D11
#define PDUT8_D12 _pdut8.bit._D12
#define PDUT8_D13 _pdut8.bit._D13
#define PDUT8_D14 _pdut8.bit._D14
#define PDUT8_D15 _pdut8.bit._D15
#define PDUT8_D _pdut8.bitc._D
__IO_EXTENDED PCN8STR _pcn8;  
#define PCN8 _pcn8.word
#define PCN8_OSEL _pcn8.bit._OSEL
#define PCN8_OE _pcn8.bit._OE
#define PCN8_IRS0 _pcn8.bit._IRS0
#define PCN8_IRS1 _pcn8.bit._IRS1
#define PCN8_IRQF _pcn8.bit._IRQF
#define PCN8_IREN _pcn8.bit._IREN
#define PCN8_EGS0 _pcn8.bit._EGS0
#define PCN8_EGS1 _pcn8.bit._EGS1
#define PCN8_PGMS _pcn8.bit._PGMS
#define PCN8_CKS0 _pcn8.bit._CKS0
#define PCN8_CKS1 _pcn8.bit._CKS1
#define PCN8_RTRG _pcn8.bit._RTRG
#define PCN8_MDSE _pcn8.bit._MDSE
#define PCN8_STGR _pcn8.bit._STGR
#define PCN8_CNTE _pcn8.bit._CNTE
#define PCN8_IRS _pcn8.bitc._IRS
#define PCN8_EGS _pcn8.bitc._EGS
#define PCN8_CKS _pcn8.bitc._CKS
__IO_EXTENDED PCNL8STR _pcnl8;  
#define PCNL8 _pcnl8.byte
#define PCNL8_OSEL _pcnl8.bit._OSEL
#define PCNL8_OE _pcnl8.bit._OE
#define PCNL8_IRS0 _pcnl8.bit._IRS0
#define PCNL8_IRS1 _pcnl8.bit._IRS1
#define PCNL8_IRQF _pcnl8.bit._IRQF
#define PCNL8_IREN _pcnl8.bit._IREN
#define PCNL8_EGS0 _pcnl8.bit._EGS0
#define PCNL8_EGS1 _pcnl8.bit._EGS1
#define PCNL8_IRS _pcnl8.bitc._IRS
#define PCNL8_EGS _pcnl8.bitc._EGS
__IO_EXTENDED PCNH8STR _pcnh8;  
#define PCNH8 _pcnh8.byte
#define PCNH8_PGMS _pcnh8.bit._PGMS
#define PCNH8_CKS0 _pcnh8.bit._CKS0
#define PCNH8_CKS1 _pcnh8.bit._CKS1
#define PCNH8_RTRG _pcnh8.bit._RTRG
#define PCNH8_MDSE _pcnh8.bit._MDSE
#define PCNH8_STGR _pcnh8.bit._STGR
#define PCNH8_CNTE _pcnh8.bit._CNTE
#define PCNH8_CKS _pcnh8.bitc._CKS
__IO_EXTENDED PTMR9STR _ptmr9;  
#define PTMR9 _ptmr9.word
#define PTMR9_D0 _ptmr9.bit._D0
#define PTMR9_D1 _ptmr9.bit._D1
#define PTMR9_D2 _ptmr9.bit._D2
#define PTMR9_D3 _ptmr9.bit._D3
#define PTMR9_D4 _ptmr9.bit._D4
#define PTMR9_D5 _ptmr9.bit._D5
#define PTMR9_D6 _ptmr9.bit._D6
#define PTMR9_D7 _ptmr9.bit._D7
#define PTMR9_D8 _ptmr9.bit._D8
#define PTMR9_D9 _ptmr9.bit._D9
#define PTMR9_D10 _ptmr9.bit._D10
#define PTMR9_D11 _ptmr9.bit._D11
#define PTMR9_D12 _ptmr9.bit._D12
#define PTMR9_D13 _ptmr9.bit._D13
#define PTMR9_D14 _ptmr9.bit._D14
#define PTMR9_D15 _ptmr9.bit._D15
#define PTMR9_D _ptmr9.bitc._D
__IO_EXTENDED PCSR9STR _pcsr9;  
#define PCSR9 _pcsr9.word
#define PCSR9_D0 _pcsr9.bit._D0
#define PCSR9_D1 _pcsr9.bit._D1
#define PCSR9_D2 _pcsr9.bit._D2
#define PCSR9_D3 _pcsr9.bit._D3
#define PCSR9_D4 _pcsr9.bit._D4
#define PCSR9_D5 _pcsr9.bit._D5
#define PCSR9_D6 _pcsr9.bit._D6
#define PCSR9_D7 _pcsr9.bit._D7
#define PCSR9_D8 _pcsr9.bit._D8
#define PCSR9_D9 _pcsr9.bit._D9
#define PCSR9_D10 _pcsr9.bit._D10
#define PCSR9_D11 _pcsr9.bit._D11
#define PCSR9_D12 _pcsr9.bit._D12
#define PCSR9_D13 _pcsr9.bit._D13
#define PCSR9_D14 _pcsr9.bit._D14
#define PCSR9_D15 _pcsr9.bit._D15
#define PCSR9_D _pcsr9.bitc._D
__IO_EXTENDED PDUT9STR _pdut9;  
#define PDUT9 _pdut9.word
#define PDUT9_D0 _pdut9.bit._D0
#define PDUT9_D1 _pdut9.bit._D1
#define PDUT9_D2 _pdut9.bit._D2
#define PDUT9_D3 _pdut9.bit._D3
#define PDUT9_D4 _pdut9.bit._D4
#define PDUT9_D5 _pdut9.bit._D5
#define PDUT9_D6 _pdut9.bit._D6
#define PDUT9_D7 _pdut9.bit._D7
#define PDUT9_D8 _pdut9.bit._D8
#define PDUT9_D9 _pdut9.bit._D9
#define PDUT9_D10 _pdut9.bit._D10
#define PDUT9_D11 _pdut9.bit._D11
#define PDUT9_D12 _pdut9.bit._D12
#define PDUT9_D13 _pdut9.bit._D13
#define PDUT9_D14 _pdut9.bit._D14
#define PDUT9_D15 _pdut9.bit._D15
#define PDUT9_D _pdut9.bitc._D
__IO_EXTENDED PCN9STR _pcn9;  
#define PCN9 _pcn9.word
#define PCN9_OSEL _pcn9.bit._OSEL
#define PCN9_OE _pcn9.bit._OE
#define PCN9_IRS0 _pcn9.bit._IRS0
#define PCN9_IRS1 _pcn9.bit._IRS1
#define PCN9_IRQF _pcn9.bit._IRQF
#define PCN9_IREN _pcn9.bit._IREN
#define PCN9_EGS0 _pcn9.bit._EGS0
#define PCN9_EGS1 _pcn9.bit._EGS1
#define PCN9_PGMS _pcn9.bit._PGMS
#define PCN9_CKS0 _pcn9.bit._CKS0
#define PCN9_CKS1 _pcn9.bit._CKS1
#define PCN9_RTRG _pcn9.bit._RTRG
#define PCN9_MDSE _pcn9.bit._MDSE
#define PCN9_STGR _pcn9.bit._STGR
#define PCN9_CNTE _pcn9.bit._CNTE
#define PCN9_IRS _pcn9.bitc._IRS
#define PCN9_EGS _pcn9.bitc._EGS
#define PCN9_CKS _pcn9.bitc._CKS
__IO_EXTENDED PCNL9STR _pcnl9;  
#define PCNL9 _pcnl9.byte
#define PCNL9_OSEL _pcnl9.bit._OSEL
#define PCNL9_OE _pcnl9.bit._OE
#define PCNL9_IRS0 _pcnl9.bit._IRS0
#define PCNL9_IRS1 _pcnl9.bit._IRS1
#define PCNL9_IRQF _pcnl9.bit._IRQF
#define PCNL9_IREN _pcnl9.bit._IREN
#define PCNL9_EGS0 _pcnl9.bit._EGS0
#define PCNL9_EGS1 _pcnl9.bit._EGS1
#define PCNL9_IRS _pcnl9.bitc._IRS
#define PCNL9_EGS _pcnl9.bitc._EGS
__IO_EXTENDED PCNH9STR _pcnh9;  
#define PCNH9 _pcnh9.byte
#define PCNH9_PGMS _pcnh9.bit._PGMS
#define PCNH9_CKS0 _pcnh9.bit._CKS0
#define PCNH9_CKS1 _pcnh9.bit._CKS1
#define PCNH9_RTRG _pcnh9.bit._RTRG
#define PCNH9_MDSE _pcnh9.bit._MDSE
#define PCNH9_STGR _pcnh9.bit._STGR
#define PCNH9_CNTE _pcnh9.bit._CNTE
#define PCNH9_CKS _pcnh9.bitc._CKS
__IO_EXTENDED PTMR10STR _ptmr10;  
#define PTMR10 _ptmr10.word
#define PTMR10_D0 _ptmr10.bit._D0
#define PTMR10_D1 _ptmr10.bit._D1
#define PTMR10_D2 _ptmr10.bit._D2
#define PTMR10_D3 _ptmr10.bit._D3
#define PTMR10_D4 _ptmr10.bit._D4
#define PTMR10_D5 _ptmr10.bit._D5
#define PTMR10_D6 _ptmr10.bit._D6
#define PTMR10_D7 _ptmr10.bit._D7
#define PTMR10_D8 _ptmr10.bit._D8
#define PTMR10_D9 _ptmr10.bit._D9
#define PTMR10_D10 _ptmr10.bit._D10
#define PTMR10_D11 _ptmr10.bit._D11
#define PTMR10_D12 _ptmr10.bit._D12
#define PTMR10_D13 _ptmr10.bit._D13
#define PTMR10_D14 _ptmr10.bit._D14
#define PTMR10_D15 _ptmr10.bit._D15
#define PTMR10_D _ptmr10.bitc._D
__IO_EXTENDED PCSR10STR _pcsr10;  
#define PCSR10 _pcsr10.word
#define PCSR10_D0 _pcsr10.bit._D0
#define PCSR10_D1 _pcsr10.bit._D1
#define PCSR10_D2 _pcsr10.bit._D2
#define PCSR10_D3 _pcsr10.bit._D3
#define PCSR10_D4 _pcsr10.bit._D4
#define PCSR10_D5 _pcsr10.bit._D5
#define PCSR10_D6 _pcsr10.bit._D6
#define PCSR10_D7 _pcsr10.bit._D7
#define PCSR10_D8 _pcsr10.bit._D8
#define PCSR10_D9 _pcsr10.bit._D9
#define PCSR10_D10 _pcsr10.bit._D10
#define PCSR10_D11 _pcsr10.bit._D11
#define PCSR10_D12 _pcsr10.bit._D12
#define PCSR10_D13 _pcsr10.bit._D13
#define PCSR10_D14 _pcsr10.bit._D14
#define PCSR10_D15 _pcsr10.bit._D15
#define PCSR10_D _pcsr10.bitc._D
__IO_EXTENDED PDUT10STR _pdut10;  
#define PDUT10 _pdut10.word
#define PDUT10_D0 _pdut10.bit._D0
#define PDUT10_D1 _pdut10.bit._D1
#define PDUT10_D2 _pdut10.bit._D2
#define PDUT10_D3 _pdut10.bit._D3
#define PDUT10_D4 _pdut10.bit._D4
#define PDUT10_D5 _pdut10.bit._D5
#define PDUT10_D6 _pdut10.bit._D6
#define PDUT10_D7 _pdut10.bit._D7
#define PDUT10_D8 _pdut10.bit._D8
#define PDUT10_D9 _pdut10.bit._D9
#define PDUT10_D10 _pdut10.bit._D10
#define PDUT10_D11 _pdut10.bit._D11
#define PDUT10_D12 _pdut10.bit._D12
#define PDUT10_D13 _pdut10.bit._D13
#define PDUT10_D14 _pdut10.bit._D14
#define PDUT10_D15 _pdut10.bit._D15
#define PDUT10_D _pdut10.bitc._D
__IO_EXTENDED PCN10STR _pcn10;  
#define PCN10 _pcn10.word
#define PCN10_OSEL _pcn10.bit._OSEL
#define PCN10_OE _pcn10.bit._OE
#define PCN10_IRS0 _pcn10.bit._IRS0
#define PCN10_IRS1 _pcn10.bit._IRS1
#define PCN10_IRQF _pcn10.bit._IRQF
#define PCN10_IREN _pcn10.bit._IREN
#define PCN10_EGS0 _pcn10.bit._EGS0
#define PCN10_EGS1 _pcn10.bit._EGS1
#define PCN10_PGMS _pcn10.bit._PGMS
#define PCN10_CKS0 _pcn10.bit._CKS0
#define PCN10_CKS1 _pcn10.bit._CKS1
#define PCN10_RTRG _pcn10.bit._RTRG
#define PCN10_MDSE _pcn10.bit._MDSE
#define PCN10_STGR _pcn10.bit._STGR
#define PCN10_CNTE _pcn10.bit._CNTE
#define PCN10_IRS _pcn10.bitc._IRS
#define PCN10_EGS _pcn10.bitc._EGS
#define PCN10_CKS _pcn10.bitc._CKS
__IO_EXTENDED PCNL10STR _pcnl10;  
#define PCNL10 _pcnl10.byte
#define PCNL10_OSEL _pcnl10.bit._OSEL
#define PCNL10_OE _pcnl10.bit._OE
#define PCNL10_IRS0 _pcnl10.bit._IRS0
#define PCNL10_IRS1 _pcnl10.bit._IRS1
#define PCNL10_IRQF _pcnl10.bit._IRQF
#define PCNL10_IREN _pcnl10.bit._IREN
#define PCNL10_EGS0 _pcnl10.bit._EGS0
#define PCNL10_EGS1 _pcnl10.bit._EGS1
#define PCNL10_IRS _pcnl10.bitc._IRS
#define PCNL10_EGS _pcnl10.bitc._EGS
__IO_EXTENDED PCNH10STR _pcnh10;  
#define PCNH10 _pcnh10.byte
#define PCNH10_PGMS _pcnh10.bit._PGMS
#define PCNH10_CKS0 _pcnh10.bit._CKS0
#define PCNH10_CKS1 _pcnh10.bit._CKS1
#define PCNH10_RTRG _pcnh10.bit._RTRG
#define PCNH10_MDSE _pcnh10.bit._MDSE
#define PCNH10_STGR _pcnh10.bit._STGR
#define PCNH10_CNTE _pcnh10.bit._CNTE
#define PCNH10_CKS _pcnh10.bitc._CKS
__IO_EXTENDED PTMR11STR _ptmr11;  
#define PTMR11 _ptmr11.word
#define PTMR11_D0 _ptmr11.bit._D0
#define PTMR11_D1 _ptmr11.bit._D1
#define PTMR11_D2 _ptmr11.bit._D2
#define PTMR11_D3 _ptmr11.bit._D3
#define PTMR11_D4 _ptmr11.bit._D4
#define PTMR11_D5 _ptmr11.bit._D5
#define PTMR11_D6 _ptmr11.bit._D6
#define PTMR11_D7 _ptmr11.bit._D7
#define PTMR11_D8 _ptmr11.bit._D8
#define PTMR11_D9 _ptmr11.bit._D9
#define PTMR11_D10 _ptmr11.bit._D10
#define PTMR11_D11 _ptmr11.bit._D11
#define PTMR11_D12 _ptmr11.bit._D12
#define PTMR11_D13 _ptmr11.bit._D13
#define PTMR11_D14 _ptmr11.bit._D14
#define PTMR11_D15 _ptmr11.bit._D15
#define PTMR11_D _ptmr11.bitc._D
__IO_EXTENDED PCSR11STR _pcsr11;  
#define PCSR11 _pcsr11.word
#define PCSR11_D0 _pcsr11.bit._D0
#define PCSR11_D1 _pcsr11.bit._D1
#define PCSR11_D2 _pcsr11.bit._D2
#define PCSR11_D3 _pcsr11.bit._D3
#define PCSR11_D4 _pcsr11.bit._D4
#define PCSR11_D5 _pcsr11.bit._D5
#define PCSR11_D6 _pcsr11.bit._D6
#define PCSR11_D7 _pcsr11.bit._D7
#define PCSR11_D8 _pcsr11.bit._D8
#define PCSR11_D9 _pcsr11.bit._D9
#define PCSR11_D10 _pcsr11.bit._D10
#define PCSR11_D11 _pcsr11.bit._D11
#define PCSR11_D12 _pcsr11.bit._D12
#define PCSR11_D13 _pcsr11.bit._D13
#define PCSR11_D14 _pcsr11.bit._D14
#define PCSR11_D15 _pcsr11.bit._D15
#define PCSR11_D _pcsr11.bitc._D
__IO_EXTENDED PDUT11STR _pdut11;  
#define PDUT11 _pdut11.word
#define PDUT11_D0 _pdut11.bit._D0
#define PDUT11_D1 _pdut11.bit._D1
#define PDUT11_D2 _pdut11.bit._D2
#define PDUT11_D3 _pdut11.bit._D3
#define PDUT11_D4 _pdut11.bit._D4
#define PDUT11_D5 _pdut11.bit._D5
#define PDUT11_D6 _pdut11.bit._D6
#define PDUT11_D7 _pdut11.bit._D7
#define PDUT11_D8 _pdut11.bit._D8
#define PDUT11_D9 _pdut11.bit._D9
#define PDUT11_D10 _pdut11.bit._D10
#define PDUT11_D11 _pdut11.bit._D11
#define PDUT11_D12 _pdut11.bit._D12
#define PDUT11_D13 _pdut11.bit._D13
#define PDUT11_D14 _pdut11.bit._D14
#define PDUT11_D15 _pdut11.bit._D15
#define PDUT11_D _pdut11.bitc._D
__IO_EXTENDED PCN11STR _pcn11;  
#define PCN11 _pcn11.word
#define PCN11_OSEL _pcn11.bit._OSEL
#define PCN11_OE _pcn11.bit._OE
#define PCN11_IRS0 _pcn11.bit._IRS0
#define PCN11_IRS1 _pcn11.bit._IRS1
#define PCN11_IRQF _pcn11.bit._IRQF
#define PCN11_IREN _pcn11.bit._IREN
#define PCN11_EGS0 _pcn11.bit._EGS0
#define PCN11_EGS1 _pcn11.bit._EGS1
#define PCN11_PGMS _pcn11.bit._PGMS
#define PCN11_CKS0 _pcn11.bit._CKS0
#define PCN11_CKS1 _pcn11.bit._CKS1
#define PCN11_RTRG _pcn11.bit._RTRG
#define PCN11_MDSE _pcn11.bit._MDSE
#define PCN11_STGR _pcn11.bit._STGR
#define PCN11_CNTE _pcn11.bit._CNTE
#define PCN11_IRS _pcn11.bitc._IRS
#define PCN11_EGS _pcn11.bitc._EGS
#define PCN11_CKS _pcn11.bitc._CKS
__IO_EXTENDED PCNL11STR _pcnl11;  
#define PCNL11 _pcnl11.byte
#define PCNL11_OSEL _pcnl11.bit._OSEL
#define PCNL11_OE _pcnl11.bit._OE
#define PCNL11_IRS0 _pcnl11.bit._IRS0
#define PCNL11_IRS1 _pcnl11.bit._IRS1
#define PCNL11_IRQF _pcnl11.bit._IRQF
#define PCNL11_IREN _pcnl11.bit._IREN
#define PCNL11_EGS0 _pcnl11.bit._EGS0
#define PCNL11_EGS1 _pcnl11.bit._EGS1
#define PCNL11_IRS _pcnl11.bitc._IRS
#define PCNL11_EGS _pcnl11.bitc._EGS
__IO_EXTENDED PCNH11STR _pcnh11;  
#define PCNH11 _pcnh11.byte
#define PCNH11_PGMS _pcnh11.bit._PGMS
#define PCNH11_CKS0 _pcnh11.bit._CKS0
#define PCNH11_CKS1 _pcnh11.bit._CKS1
#define PCNH11_RTRG _pcnh11.bit._RTRG
#define PCNH11_MDSE _pcnh11.bit._MDSE
#define PCNH11_STGR _pcnh11.bit._STGR
#define PCNH11_CNTE _pcnh11.bit._CNTE
#define PCNH11_CKS _pcnh11.bitc._CKS
__IO_EXTENDED GCN13STR _gcn13;  
#define GCN13 _gcn13.word
#define GCN13_TSEL00 _gcn13.bit._TSEL00
#define GCN13_TSEL01 _gcn13.bit._TSEL01
#define GCN13_TSEL02 _gcn13.bit._TSEL02
#define GCN13_TSEL03 _gcn13.bit._TSEL03
#define GCN13_TSEL10 _gcn13.bit._TSEL10
#define GCN13_TSEL11 _gcn13.bit._TSEL11
#define GCN13_TSEL12 _gcn13.bit._TSEL12
#define GCN13_TSEL13 _gcn13.bit._TSEL13
#define GCN13_TSEL20 _gcn13.bit._TSEL20
#define GCN13_TSEL21 _gcn13.bit._TSEL21
#define GCN13_TSEL22 _gcn13.bit._TSEL22
#define GCN13_TSEL23 _gcn13.bit._TSEL23
#define GCN13_TSEL30 _gcn13.bit._TSEL30
#define GCN13_TSEL31 _gcn13.bit._TSEL31
#define GCN13_TSEL32 _gcn13.bit._TSEL32
#define GCN13_TSEL33 _gcn13.bit._TSEL33
#define GCN13_TSEL0 _gcn13.bitc._TSEL0
#define GCN13_TSEL1 _gcn13.bitc._TSEL1
#define GCN13_TSEL2 _gcn13.bitc._TSEL2
#define GCN13_TSEL3 _gcn13.bitc._TSEL3
__IO_EXTENDED GCN1L3STR _gcn1l3;  
#define GCN1L3 _gcn1l3.byte
#define GCN1L3_TSEL00 _gcn1l3.bit._TSEL00
#define GCN1L3_TSEL01 _gcn1l3.bit._TSEL01
#define GCN1L3_TSEL02 _gcn1l3.bit._TSEL02
#define GCN1L3_TSEL03 _gcn1l3.bit._TSEL03
#define GCN1L3_TSEL10 _gcn1l3.bit._TSEL10
#define GCN1L3_TSEL11 _gcn1l3.bit._TSEL11
#define GCN1L3_TSEL12 _gcn1l3.bit._TSEL12
#define GCN1L3_TSEL13 _gcn1l3.bit._TSEL13
#define GCN1L3_TSEL0 _gcn1l3.bitc._TSEL0
#define GCN1L3_TSEL1 _gcn1l3.bitc._TSEL1
__IO_EXTENDED GCN1H3STR _gcn1h3;  
#define GCN1H3 _gcn1h3.byte
#define GCN1H3_TSEL20 _gcn1h3.bit._TSEL20
#define GCN1H3_TSEL21 _gcn1h3.bit._TSEL21
#define GCN1H3_TSEL22 _gcn1h3.bit._TSEL22
#define GCN1H3_TSEL23 _gcn1h3.bit._TSEL23
#define GCN1H3_TSEL30 _gcn1h3.bit._TSEL30
#define GCN1H3_TSEL31 _gcn1h3.bit._TSEL31
#define GCN1H3_TSEL32 _gcn1h3.bit._TSEL32
#define GCN1H3_TSEL33 _gcn1h3.bit._TSEL33
#define GCN1H3_TSEL2 _gcn1h3.bitc._TSEL2
#define GCN1H3_TSEL3 _gcn1h3.bitc._TSEL3
__IO_EXTENDED GCN23STR _gcn23;  
#define GCN23 _gcn23.word
#define GCN23_EN0 _gcn23.bit._EN0
#define GCN23_EN1 _gcn23.bit._EN1
#define GCN23_EN2 _gcn23.bit._EN2
#define GCN23_EN3 _gcn23.bit._EN3
#define GCN23_CKSEL0 _gcn23.bit._CKSEL0
#define GCN23_CKSEL1 _gcn23.bit._CKSEL1
#define GCN23_CKSEL2 _gcn23.bit._CKSEL2
#define GCN23_CKSEL3 _gcn23.bit._CKSEL3
#define GCN23_EN _gcn23.bitc._EN
#define GCN23_CKSEL _gcn23.bitc._CKSEL
__IO_EXTENDED GCN2L3STR _gcn2l3;  
#define GCN2L3 _gcn2l3.byte
#define GCN2L3_EN0 _gcn2l3.bit._EN0
#define GCN2L3_EN1 _gcn2l3.bit._EN1
#define GCN2L3_EN2 _gcn2l3.bit._EN2
#define GCN2L3_EN3 _gcn2l3.bit._EN3
#define GCN2L3_EN _gcn2l3.bitc._EN
__IO_EXTENDED GCN2H3STR _gcn2h3;  
#define GCN2H3 _gcn2h3.byte
#define GCN2H3_CKSEL0 _gcn2h3.bit._CKSEL0
#define GCN2H3_CKSEL1 _gcn2h3.bit._CKSEL1
#define GCN2H3_CKSEL2 _gcn2h3.bit._CKSEL2
#define GCN2H3_CKSEL3 _gcn2h3.bit._CKSEL3
#define GCN2H3_CKSEL _gcn2h3.bitc._CKSEL
__IO_EXTENDED PTMR12STR _ptmr12;  
#define PTMR12 _ptmr12.word
#define PTMR12_D0 _ptmr12.bit._D0
#define PTMR12_D1 _ptmr12.bit._D1
#define PTMR12_D2 _ptmr12.bit._D2
#define PTMR12_D3 _ptmr12.bit._D3
#define PTMR12_D4 _ptmr12.bit._D4
#define PTMR12_D5 _ptmr12.bit._D5
#define PTMR12_D6 _ptmr12.bit._D6
#define PTMR12_D7 _ptmr12.bit._D7
#define PTMR12_D8 _ptmr12.bit._D8
#define PTMR12_D9 _ptmr12.bit._D9
#define PTMR12_D10 _ptmr12.bit._D10
#define PTMR12_D11 _ptmr12.bit._D11
#define PTMR12_D12 _ptmr12.bit._D12
#define PTMR12_D13 _ptmr12.bit._D13
#define PTMR12_D14 _ptmr12.bit._D14
#define PTMR12_D15 _ptmr12.bit._D15
#define PTMR12_D _ptmr12.bitc._D
__IO_EXTENDED PCSR12STR _pcsr12;  
#define PCSR12 _pcsr12.word
#define PCSR12_D0 _pcsr12.bit._D0
#define PCSR12_D1 _pcsr12.bit._D1
#define PCSR12_D2 _pcsr12.bit._D2
#define PCSR12_D3 _pcsr12.bit._D3
#define PCSR12_D4 _pcsr12.bit._D4
#define PCSR12_D5 _pcsr12.bit._D5
#define PCSR12_D6 _pcsr12.bit._D6
#define PCSR12_D7 _pcsr12.bit._D7
#define PCSR12_D8 _pcsr12.bit._D8
#define PCSR12_D9 _pcsr12.bit._D9
#define PCSR12_D10 _pcsr12.bit._D10
#define PCSR12_D11 _pcsr12.bit._D11
#define PCSR12_D12 _pcsr12.bit._D12
#define PCSR12_D13 _pcsr12.bit._D13
#define PCSR12_D14 _pcsr12.bit._D14
#define PCSR12_D15 _pcsr12.bit._D15
#define PCSR12_D _pcsr12.bitc._D
__IO_EXTENDED PDUT12STR _pdut12;  
#define PDUT12 _pdut12.word
#define PDUT12_D0 _pdut12.bit._D0
#define PDUT12_D1 _pdut12.bit._D1
#define PDUT12_D2 _pdut12.bit._D2
#define PDUT12_D3 _pdut12.bit._D3
#define PDUT12_D4 _pdut12.bit._D4
#define PDUT12_D5 _pdut12.bit._D5
#define PDUT12_D6 _pdut12.bit._D6
#define PDUT12_D7 _pdut12.bit._D7
#define PDUT12_D8 _pdut12.bit._D8
#define PDUT12_D9 _pdut12.bit._D9
#define PDUT12_D10 _pdut12.bit._D10
#define PDUT12_D11 _pdut12.bit._D11
#define PDUT12_D12 _pdut12.bit._D12
#define PDUT12_D13 _pdut12.bit._D13
#define PDUT12_D14 _pdut12.bit._D14
#define PDUT12_D15 _pdut12.bit._D15
#define PDUT12_D _pdut12.bitc._D
__IO_EXTENDED PCN12STR _pcn12;  
#define PCN12 _pcn12.word
#define PCN12_OSEL _pcn12.bit._OSEL
#define PCN12_OE _pcn12.bit._OE
#define PCN12_IRS0 _pcn12.bit._IRS0
#define PCN12_IRS1 _pcn12.bit._IRS1
#define PCN12_IRQF _pcn12.bit._IRQF
#define PCN12_IREN _pcn12.bit._IREN
#define PCN12_EGS0 _pcn12.bit._EGS0
#define PCN12_EGS1 _pcn12.bit._EGS1
#define PCN12_PGMS _pcn12.bit._PGMS
#define PCN12_CKS0 _pcn12.bit._CKS0
#define PCN12_CKS1 _pcn12.bit._CKS1
#define PCN12_RTRG _pcn12.bit._RTRG
#define PCN12_MDSE _pcn12.bit._MDSE
#define PCN12_STGR _pcn12.bit._STGR
#define PCN12_CNTE _pcn12.bit._CNTE
#define PCN12_IRS _pcn12.bitc._IRS
#define PCN12_EGS _pcn12.bitc._EGS
#define PCN12_CKS _pcn12.bitc._CKS
__IO_EXTENDED PCNL12STR _pcnl12;  
#define PCNL12 _pcnl12.byte
#define PCNL12_OSEL _pcnl12.bit._OSEL
#define PCNL12_OE _pcnl12.bit._OE
#define PCNL12_IRS0 _pcnl12.bit._IRS0
#define PCNL12_IRS1 _pcnl12.bit._IRS1
#define PCNL12_IRQF _pcnl12.bit._IRQF
#define PCNL12_IREN _pcnl12.bit._IREN
#define PCNL12_EGS0 _pcnl12.bit._EGS0
#define PCNL12_EGS1 _pcnl12.bit._EGS1
#define PCNL12_IRS _pcnl12.bitc._IRS
#define PCNL12_EGS _pcnl12.bitc._EGS
__IO_EXTENDED PCNH12STR _pcnh12;  
#define PCNH12 _pcnh12.byte
#define PCNH12_PGMS _pcnh12.bit._PGMS
#define PCNH12_CKS0 _pcnh12.bit._CKS0
#define PCNH12_CKS1 _pcnh12.bit._CKS1
#define PCNH12_RTRG _pcnh12.bit._RTRG
#define PCNH12_MDSE _pcnh12.bit._MDSE
#define PCNH12_STGR _pcnh12.bit._STGR
#define PCNH12_CNTE _pcnh12.bit._CNTE
#define PCNH12_CKS _pcnh12.bitc._CKS
__IO_EXTENDED PTMR13STR _ptmr13;  
#define PTMR13 _ptmr13.word
#define PTMR13_D0 _ptmr13.bit._D0
#define PTMR13_D1 _ptmr13.bit._D1
#define PTMR13_D2 _ptmr13.bit._D2
#define PTMR13_D3 _ptmr13.bit._D3
#define PTMR13_D4 _ptmr13.bit._D4
#define PTMR13_D5 _ptmr13.bit._D5
#define PTMR13_D6 _ptmr13.bit._D6
#define PTMR13_D7 _ptmr13.bit._D7
#define PTMR13_D8 _ptmr13.bit._D8
#define PTMR13_D9 _ptmr13.bit._D9
#define PTMR13_D10 _ptmr13.bit._D10
#define PTMR13_D11 _ptmr13.bit._D11
#define PTMR13_D12 _ptmr13.bit._D12
#define PTMR13_D13 _ptmr13.bit._D13
#define PTMR13_D14 _ptmr13.bit._D14
#define PTMR13_D15 _ptmr13.bit._D15
#define PTMR13_D _ptmr13.bitc._D
__IO_EXTENDED PCSR13STR _pcsr13;  
#define PCSR13 _pcsr13.word
#define PCSR13_D0 _pcsr13.bit._D0
#define PCSR13_D1 _pcsr13.bit._D1
#define PCSR13_D2 _pcsr13.bit._D2
#define PCSR13_D3 _pcsr13.bit._D3
#define PCSR13_D4 _pcsr13.bit._D4
#define PCSR13_D5 _pcsr13.bit._D5
#define PCSR13_D6 _pcsr13.bit._D6
#define PCSR13_D7 _pcsr13.bit._D7
#define PCSR13_D8 _pcsr13.bit._D8
#define PCSR13_D9 _pcsr13.bit._D9
#define PCSR13_D10 _pcsr13.bit._D10
#define PCSR13_D11 _pcsr13.bit._D11
#define PCSR13_D12 _pcsr13.bit._D12
#define PCSR13_D13 _pcsr13.bit._D13
#define PCSR13_D14 _pcsr13.bit._D14
#define PCSR13_D15 _pcsr13.bit._D15
#define PCSR13_D _pcsr13.bitc._D
__IO_EXTENDED PDUT13STR _pdut13;  
#define PDUT13 _pdut13.word
#define PDUT13_D0 _pdut13.bit._D0
#define PDUT13_D1 _pdut13.bit._D1
#define PDUT13_D2 _pdut13.bit._D2
#define PDUT13_D3 _pdut13.bit._D3
#define PDUT13_D4 _pdut13.bit._D4
#define PDUT13_D5 _pdut13.bit._D5
#define PDUT13_D6 _pdut13.bit._D6
#define PDUT13_D7 _pdut13.bit._D7
#define PDUT13_D8 _pdut13.bit._D8
#define PDUT13_D9 _pdut13.bit._D9
#define PDUT13_D10 _pdut13.bit._D10
#define PDUT13_D11 _pdut13.bit._D11
#define PDUT13_D12 _pdut13.bit._D12
#define PDUT13_D13 _pdut13.bit._D13
#define PDUT13_D14 _pdut13.bit._D14
#define PDUT13_D15 _pdut13.bit._D15
#define PDUT13_D _pdut13.bitc._D
__IO_EXTENDED PCN13STR _pcn13;  
#define PCN13 _pcn13.word
#define PCN13_OSEL _pcn13.bit._OSEL
#define PCN13_OE _pcn13.bit._OE
#define PCN13_IRS0 _pcn13.bit._IRS0
#define PCN13_IRS1 _pcn13.bit._IRS1
#define PCN13_IRQF _pcn13.bit._IRQF
#define PCN13_IREN _pcn13.bit._IREN
#define PCN13_EGS0 _pcn13.bit._EGS0
#define PCN13_EGS1 _pcn13.bit._EGS1
#define PCN13_PGMS _pcn13.bit._PGMS
#define PCN13_CKS0 _pcn13.bit._CKS0
#define PCN13_CKS1 _pcn13.bit._CKS1
#define PCN13_RTRG _pcn13.bit._RTRG
#define PCN13_MDSE _pcn13.bit._MDSE
#define PCN13_STGR _pcn13.bit._STGR
#define PCN13_CNTE _pcn13.bit._CNTE
#define PCN13_IRS _pcn13.bitc._IRS
#define PCN13_EGS _pcn13.bitc._EGS
#define PCN13_CKS _pcn13.bitc._CKS
__IO_EXTENDED PCNL13STR _pcnl13;  
#define PCNL13 _pcnl13.byte
#define PCNL13_OSEL _pcnl13.bit._OSEL
#define PCNL13_OE _pcnl13.bit._OE
#define PCNL13_IRS0 _pcnl13.bit._IRS0
#define PCNL13_IRS1 _pcnl13.bit._IRS1
#define PCNL13_IRQF _pcnl13.bit._IRQF
#define PCNL13_IREN _pcnl13.bit._IREN
#define PCNL13_EGS0 _pcnl13.bit._EGS0
#define PCNL13_EGS1 _pcnl13.bit._EGS1
#define PCNL13_IRS _pcnl13.bitc._IRS
#define PCNL13_EGS _pcnl13.bitc._EGS
__IO_EXTENDED PCNH13STR _pcnh13;  
#define PCNH13 _pcnh13.byte
#define PCNH13_PGMS _pcnh13.bit._PGMS
#define PCNH13_CKS0 _pcnh13.bit._CKS0
#define PCNH13_CKS1 _pcnh13.bit._CKS1
#define PCNH13_RTRG _pcnh13.bit._RTRG
#define PCNH13_MDSE _pcnh13.bit._MDSE
#define PCNH13_STGR _pcnh13.bit._STGR
#define PCNH13_CNTE _pcnh13.bit._CNTE
#define PCNH13_CKS _pcnh13.bitc._CKS
__IO_EXTENDED PTMR14STR _ptmr14;  
#define PTMR14 _ptmr14.word
#define PTMR14_D0 _ptmr14.bit._D0
#define PTMR14_D1 _ptmr14.bit._D1
#define PTMR14_D2 _ptmr14.bit._D2
#define PTMR14_D3 _ptmr14.bit._D3
#define PTMR14_D4 _ptmr14.bit._D4
#define PTMR14_D5 _ptmr14.bit._D5
#define PTMR14_D6 _ptmr14.bit._D6
#define PTMR14_D7 _ptmr14.bit._D7
#define PTMR14_D8 _ptmr14.bit._D8
#define PTMR14_D9 _ptmr14.bit._D9
#define PTMR14_D10 _ptmr14.bit._D10
#define PTMR14_D11 _ptmr14.bit._D11
#define PTMR14_D12 _ptmr14.bit._D12
#define PTMR14_D13 _ptmr14.bit._D13
#define PTMR14_D14 _ptmr14.bit._D14
#define PTMR14_D15 _ptmr14.bit._D15
#define PTMR14_D _ptmr14.bitc._D
__IO_EXTENDED PCSR14STR _pcsr14;  
#define PCSR14 _pcsr14.word
#define PCSR14_D0 _pcsr14.bit._D0
#define PCSR14_D1 _pcsr14.bit._D1
#define PCSR14_D2 _pcsr14.bit._D2
#define PCSR14_D3 _pcsr14.bit._D3
#define PCSR14_D4 _pcsr14.bit._D4
#define PCSR14_D5 _pcsr14.bit._D5
#define PCSR14_D6 _pcsr14.bit._D6
#define PCSR14_D7 _pcsr14.bit._D7
#define PCSR14_D8 _pcsr14.bit._D8
#define PCSR14_D9 _pcsr14.bit._D9
#define PCSR14_D10 _pcsr14.bit._D10
#define PCSR14_D11 _pcsr14.bit._D11
#define PCSR14_D12 _pcsr14.bit._D12
#define PCSR14_D13 _pcsr14.bit._D13
#define PCSR14_D14 _pcsr14.bit._D14
#define PCSR14_D15 _pcsr14.bit._D15
#define PCSR14_D _pcsr14.bitc._D
__IO_EXTENDED PDUT14STR _pdut14;  
#define PDUT14 _pdut14.word
#define PDUT14_D0 _pdut14.bit._D0
#define PDUT14_D1 _pdut14.bit._D1
#define PDUT14_D2 _pdut14.bit._D2
#define PDUT14_D3 _pdut14.bit._D3
#define PDUT14_D4 _pdut14.bit._D4
#define PDUT14_D5 _pdut14.bit._D5
#define PDUT14_D6 _pdut14.bit._D6
#define PDUT14_D7 _pdut14.bit._D7
#define PDUT14_D8 _pdut14.bit._D8
#define PDUT14_D9 _pdut14.bit._D9
#define PDUT14_D10 _pdut14.bit._D10
#define PDUT14_D11 _pdut14.bit._D11
#define PDUT14_D12 _pdut14.bit._D12
#define PDUT14_D13 _pdut14.bit._D13
#define PDUT14_D14 _pdut14.bit._D14
#define PDUT14_D15 _pdut14.bit._D15
#define PDUT14_D _pdut14.bitc._D
__IO_EXTENDED PCN14STR _pcn14;  
#define PCN14 _pcn14.word
#define PCN14_OSEL _pcn14.bit._OSEL
#define PCN14_OE _pcn14.bit._OE
#define PCN14_IRS0 _pcn14.bit._IRS0
#define PCN14_IRS1 _pcn14.bit._IRS1
#define PCN14_IRQF _pcn14.bit._IRQF
#define PCN14_IREN _pcn14.bit._IREN
#define PCN14_EGS0 _pcn14.bit._EGS0
#define PCN14_EGS1 _pcn14.bit._EGS1
#define PCN14_PGMS _pcn14.bit._PGMS
#define PCN14_CKS0 _pcn14.bit._CKS0
#define PCN14_CKS1 _pcn14.bit._CKS1
#define PCN14_RTRG _pcn14.bit._RTRG
#define PCN14_MDSE _pcn14.bit._MDSE
#define PCN14_STGR _pcn14.bit._STGR
#define PCN14_CNTE _pcn14.bit._CNTE
#define PCN14_IRS _pcn14.bitc._IRS
#define PCN14_EGS _pcn14.bitc._EGS
#define PCN14_CKS _pcn14.bitc._CKS
__IO_EXTENDED PCNL14STR _pcnl14;  
#define PCNL14 _pcnl14.byte
#define PCNL14_OSEL _pcnl14.bit._OSEL
#define PCNL14_OE _pcnl14.bit._OE
#define PCNL14_IRS0 _pcnl14.bit._IRS0
#define PCNL14_IRS1 _pcnl14.bit._IRS1
#define PCNL14_IRQF _pcnl14.bit._IRQF
#define PCNL14_IREN _pcnl14.bit._IREN
#define PCNL14_EGS0 _pcnl14.bit._EGS0
#define PCNL14_EGS1 _pcnl14.bit._EGS1
#define PCNL14_IRS _pcnl14.bitc._IRS
#define PCNL14_EGS _pcnl14.bitc._EGS
__IO_EXTENDED PCNH14STR _pcnh14;  
#define PCNH14 _pcnh14.byte
#define PCNH14_PGMS _pcnh14.bit._PGMS
#define PCNH14_CKS0 _pcnh14.bit._CKS0
#define PCNH14_CKS1 _pcnh14.bit._CKS1
#define PCNH14_RTRG _pcnh14.bit._RTRG
#define PCNH14_MDSE _pcnh14.bit._MDSE
#define PCNH14_STGR _pcnh14.bit._STGR
#define PCNH14_CNTE _pcnh14.bit._CNTE
#define PCNH14_CKS _pcnh14.bitc._CKS
__IO_EXTENDED PTMR15STR _ptmr15;  
#define PTMR15 _ptmr15.word
#define PTMR15_D0 _ptmr15.bit._D0
#define PTMR15_D1 _ptmr15.bit._D1
#define PTMR15_D2 _ptmr15.bit._D2
#define PTMR15_D3 _ptmr15.bit._D3
#define PTMR15_D4 _ptmr15.bit._D4
#define PTMR15_D5 _ptmr15.bit._D5
#define PTMR15_D6 _ptmr15.bit._D6
#define PTMR15_D7 _ptmr15.bit._D7
#define PTMR15_D8 _ptmr15.bit._D8
#define PTMR15_D9 _ptmr15.bit._D9
#define PTMR15_D10 _ptmr15.bit._D10
#define PTMR15_D11 _ptmr15.bit._D11
#define PTMR15_D12 _ptmr15.bit._D12
#define PTMR15_D13 _ptmr15.bit._D13
#define PTMR15_D14 _ptmr15.bit._D14
#define PTMR15_D15 _ptmr15.bit._D15
#define PTMR15_D _ptmr15.bitc._D
__IO_EXTENDED PCSR15STR _pcsr15;  
#define PCSR15 _pcsr15.word
#define PCSR15_D0 _pcsr15.bit._D0
#define PCSR15_D1 _pcsr15.bit._D1
#define PCSR15_D2 _pcsr15.bit._D2
#define PCSR15_D3 _pcsr15.bit._D3
#define PCSR15_D4 _pcsr15.bit._D4
#define PCSR15_D5 _pcsr15.bit._D5
#define PCSR15_D6 _pcsr15.bit._D6
#define PCSR15_D7 _pcsr15.bit._D7
#define PCSR15_D8 _pcsr15.bit._D8
#define PCSR15_D9 _pcsr15.bit._D9
#define PCSR15_D10 _pcsr15.bit._D10
#define PCSR15_D11 _pcsr15.bit._D11
#define PCSR15_D12 _pcsr15.bit._D12
#define PCSR15_D13 _pcsr15.bit._D13
#define PCSR15_D14 _pcsr15.bit._D14
#define PCSR15_D15 _pcsr15.bit._D15
#define PCSR15_D _pcsr15.bitc._D
__IO_EXTENDED PDUT15STR _pdut15;  
#define PDUT15 _pdut15.word
#define PDUT15_D0 _pdut15.bit._D0
#define PDUT15_D1 _pdut15.bit._D1
#define PDUT15_D2 _pdut15.bit._D2
#define PDUT15_D3 _pdut15.bit._D3
#define PDUT15_D4 _pdut15.bit._D4
#define PDUT15_D5 _pdut15.bit._D5
#define PDUT15_D6 _pdut15.bit._D6
#define PDUT15_D7 _pdut15.bit._D7
#define PDUT15_D8 _pdut15.bit._D8
#define PDUT15_D9 _pdut15.bit._D9
#define PDUT15_D10 _pdut15.bit._D10
#define PDUT15_D11 _pdut15.bit._D11
#define PDUT15_D12 _pdut15.bit._D12
#define PDUT15_D13 _pdut15.bit._D13
#define PDUT15_D14 _pdut15.bit._D14
#define PDUT15_D15 _pdut15.bit._D15
#define PDUT15_D _pdut15.bitc._D
__IO_EXTENDED PCN15STR _pcn15;  
#define PCN15 _pcn15.word
#define PCN15_OSEL _pcn15.bit._OSEL
#define PCN15_OE _pcn15.bit._OE
#define PCN15_IRS0 _pcn15.bit._IRS0
#define PCN15_IRS1 _pcn15.bit._IRS1
#define PCN15_IRQF _pcn15.bit._IRQF
#define PCN15_IREN _pcn15.bit._IREN
#define PCN15_EGS0 _pcn15.bit._EGS0
#define PCN15_EGS1 _pcn15.bit._EGS1
#define PCN15_PGMS _pcn15.bit._PGMS
#define PCN15_CKS0 _pcn15.bit._CKS0
#define PCN15_CKS1 _pcn15.bit._CKS1
#define PCN15_RTRG _pcn15.bit._RTRG
#define PCN15_MDSE _pcn15.bit._MDSE
#define PCN15_STGR _pcn15.bit._STGR
#define PCN15_CNTE _pcn15.bit._CNTE
#define PCN15_IRS _pcn15.bitc._IRS
#define PCN15_EGS _pcn15.bitc._EGS
#define PCN15_CKS _pcn15.bitc._CKS
__IO_EXTENDED PCNL15STR _pcnl15;  
#define PCNL15 _pcnl15.byte
#define PCNL15_OSEL _pcnl15.bit._OSEL
#define PCNL15_OE _pcnl15.bit._OE
#define PCNL15_IRS0 _pcnl15.bit._IRS0
#define PCNL15_IRS1 _pcnl15.bit._IRS1
#define PCNL15_IRQF _pcnl15.bit._IRQF
#define PCNL15_IREN _pcnl15.bit._IREN
#define PCNL15_EGS0 _pcnl15.bit._EGS0
#define PCNL15_EGS1 _pcnl15.bit._EGS1
#define PCNL15_IRS _pcnl15.bitc._IRS
#define PCNL15_EGS _pcnl15.bitc._EGS
__IO_EXTENDED PCNH15STR _pcnh15;  
#define PCNH15 _pcnh15.byte
#define PCNH15_PGMS _pcnh15.bit._PGMS
#define PCNH15_CKS0 _pcnh15.bit._CKS0
#define PCNH15_CKS1 _pcnh15.bit._CKS1
#define PCNH15_RTRG _pcnh15.bit._RTRG
#define PCNH15_MDSE _pcnh15.bit._MDSE
#define PCNH15_STGR _pcnh15.bit._STGR
#define PCNH15_CNTE _pcnh15.bit._CNTE
#define PCNH15_CKS _pcnh15.bitc._CKS
__IO_EXTENDED PRRR10STR _prrr10;  
#define PRRR10 _prrr10.byte
#define PRRR10_PPG8_R _prrr10.bit._PPG8_R
#define PRRR10_PPG9_R _prrr10.bit._PPG9_R
#define PRRR10_PPG10_R _prrr10.bit._PPG10_R
#define PRRR10_PPG11_R _prrr10.bit._PPG11_R
#define PRRR10_TTG8_R _prrr10.bit._TTG8_R
#define PRRR10_TTG9_R _prrr10.bit._TTG9_R
#define PRRR10_TTG10_R _prrr10.bit._TTG10_R
#define PRRR10_TTG11_R _prrr10.bit._TTG11_R
__IO_EXTENDED PRRR11STR _prrr11;  
#define PRRR11 _prrr11.byte
#define PRRR11_PPG16_R _prrr11.bit._PPG16_R
#define PRRR11_PPG17_R _prrr11.bit._PPG17_R
#define PRRR11_PPG18_R _prrr11.bit._PPG18_R
#define PRRR11_PPG19_R _prrr11.bit._PPG19_R
#define PRRR11_TTG16_R _prrr11.bit._TTG16_R
#define PRRR11_TTG17_R _prrr11.bit._TTG17_R
#define PRRR11_TTG18_R _prrr11.bit._TTG18_R
#define PRRR11_TTG19_R _prrr11.bit._TTG19_R
__IO_EXTENDED PRRR12STR _prrr12;  
#define PRRR12 _prrr12.byte
#define PRRR12_CS0_R _prrr12.bit._CS0_R
#define PRRR12_CS1_R _prrr12.bit._CS1_R
#define PRRR12_CS2_R _prrr12.bit._CS2_R
#define PRRR12_CS4_R _prrr12.bit._CS4_R
#define PRRR12_CS5_R _prrr12.bit._CS5_R
__IO_EXTENDED PRRR13STR _prrr13;  
#define PRRR13 _prrr13.byte
__IO_EXTENDED EAC0STR _eac0;  
#define EAC0 _eac0.word
#define EAC0_R0 _eac0.bit._R0
#define EAC0_R1 _eac0.bit._R1
#define EAC0_R2 _eac0.bit._R2
#define EAC0_ACE _eac0.bit._ACE
#define EAC0_STS _eac0.bit._STS
#define EAC0_WSF _eac0.bit._WSF
#define EAC0_ES _eac0.bit._ES
#define EAC0_BW _eac0.bit._BW
#define EAC0_CSE _eac0.bit._CSE
#define EAC0_CSL _eac0.bit._CSL
#define EAC0_ATL _eac0.bit._ATL
#define EAC0_R _eac0.bitc._R
__IO_EXTENDED EACL0STR _eacl0;  
#define EACL0 _eacl0.byte
#define EACL0_R0 _eacl0.bit._R0
#define EACL0_R1 _eacl0.bit._R1
#define EACL0_R2 _eacl0.bit._R2
#define EACL0_ACE _eacl0.bit._ACE
#define EACL0_STS _eacl0.bit._STS
#define EACL0_WSF _eacl0.bit._WSF
#define EACL0_ES _eacl0.bit._ES
#define EACL0_BW _eacl0.bit._BW
#define EACL0_R _eacl0.bitc._R
__IO_EXTENDED EACH0STR _each0;  
#define EACH0 _each0.byte
#define EACH0_CSE _each0.bit._CSE
#define EACH0_CSL _each0.bit._CSL
#define EACH0_ATL _each0.bit._ATL
__IO_EXTENDED EAC1STR _eac1;  
#define EAC1 _eac1.word
#define EAC1_R0 _eac1.bit._R0
#define EAC1_R1 _eac1.bit._R1
#define EAC1_R2 _eac1.bit._R2
#define EAC1_ACE _eac1.bit._ACE
#define EAC1_STS _eac1.bit._STS
#define EAC1_WSF _eac1.bit._WSF
#define EAC1_ES _eac1.bit._ES
#define EAC1_BW _eac1.bit._BW
#define EAC1_CSE _eac1.bit._CSE
#define EAC1_CSL _eac1.bit._CSL
#define EAC1_ATL _eac1.bit._ATL
#define EAC1_R _eac1.bitc._R
__IO_EXTENDED EACL1STR _eacl1;  
#define EACL1 _eacl1.byte
#define EACL1_R0 _eacl1.bit._R0
#define EACL1_R1 _eacl1.bit._R1
#define EACL1_R2 _eacl1.bit._R2
#define EACL1_ACE _eacl1.bit._ACE
#define EACL1_STS _eacl1.bit._STS
#define EACL1_WSF _eacl1.bit._WSF
#define EACL1_ES _eacl1.bit._ES
#define EACL1_BW _eacl1.bit._BW
#define EACL1_R _eacl1.bitc._R
__IO_EXTENDED EACH1STR _each1;  
#define EACH1 _each1.byte
#define EACH1_CSE _each1.bit._CSE
#define EACH1_CSL _each1.bit._CSL
#define EACH1_ATL _each1.bit._ATL
__IO_EXTENDED EAC2STR _eac2;  
#define EAC2 _eac2.word
#define EAC2_R0 _eac2.bit._R0
#define EAC2_R1 _eac2.bit._R1
#define EAC2_R2 _eac2.bit._R2
#define EAC2_ACE _eac2.bit._ACE
#define EAC2_STS _eac2.bit._STS
#define EAC2_WSF _eac2.bit._WSF
#define EAC2_ES _eac2.bit._ES
#define EAC2_BW _eac2.bit._BW
#define EAC2_EASZ0 _eac2.bit._EASZ0
#define EAC2_EASZ1 _eac2.bit._EASZ1
#define EAC2_EASZ2 _eac2.bit._EASZ2
#define EAC2_CSE _eac2.bit._CSE
#define EAC2_CSL _eac2.bit._CSL
#define EAC2_ATL _eac2.bit._ATL
#define EAC2_R _eac2.bitc._R
#define EAC2_EASZ _eac2.bitc._EASZ
__IO_EXTENDED EACL2STR _eacl2;  
#define EACL2 _eacl2.byte
#define EACL2_R0 _eacl2.bit._R0
#define EACL2_R1 _eacl2.bit._R1
#define EACL2_R2 _eacl2.bit._R2
#define EACL2_ACE _eacl2.bit._ACE
#define EACL2_STS _eacl2.bit._STS
#define EACL2_WSF _eacl2.bit._WSF
#define EACL2_ES _eacl2.bit._ES
#define EACL2_BW _eacl2.bit._BW
#define EACL2_R _eacl2.bitc._R
__IO_EXTENDED EACH2STR _each2;  
#define EACH2 _each2.byte
#define EACH2_EASZ0 _each2.bit._EASZ0
#define EACH2_EASZ1 _each2.bit._EASZ1
#define EACH2_EASZ2 _each2.bit._EASZ2
#define EACH2_CSE _each2.bit._CSE
#define EACH2_CSL _each2.bit._CSL
#define EACH2_ATL _each2.bit._ATL
#define EACH2_EASZ _each2.bitc._EASZ
__IO_EXTENDED EAC3STR _eac3;  
#define EAC3 _eac3.word
#define EAC3_R0 _eac3.bit._R0
#define EAC3_R1 _eac3.bit._R1
#define EAC3_R2 _eac3.bit._R2
#define EAC3_ACE _eac3.bit._ACE
#define EAC3_STS _eac3.bit._STS
#define EAC3_WSF _eac3.bit._WSF
#define EAC3_ES _eac3.bit._ES
#define EAC3_BW _eac3.bit._BW
#define EAC3_EASZ0 _eac3.bit._EASZ0
#define EAC3_EASZ1 _eac3.bit._EASZ1
#define EAC3_EASZ2 _eac3.bit._EASZ2
#define EAC3_CSE _eac3.bit._CSE
#define EAC3_CSL _eac3.bit._CSL
#define EAC3_ATL _eac3.bit._ATL
#define EAC3_R _eac3.bitc._R
#define EAC3_EASZ _eac3.bitc._EASZ
__IO_EXTENDED EACL3STR _eacl3;  
#define EACL3 _eacl3.byte
#define EACL3_R0 _eacl3.bit._R0
#define EACL3_R1 _eacl3.bit._R1
#define EACL3_R2 _eacl3.bit._R2
#define EACL3_ACE _eacl3.bit._ACE
#define EACL3_STS _eacl3.bit._STS
#define EACL3_WSF _eacl3.bit._WSF
#define EACL3_ES _eacl3.bit._ES
#define EACL3_BW _eacl3.bit._BW
#define EACL3_R _eacl3.bitc._R
__IO_EXTENDED EACH3STR _each3;  
#define EACH3 _each3.byte
#define EACH3_EASZ0 _each3.bit._EASZ0
#define EACH3_EASZ1 _each3.bit._EASZ1
#define EACH3_EASZ2 _each3.bit._EASZ2
#define EACH3_CSE _each3.bit._CSE
#define EACH3_CSL _each3.bit._CSL
#define EACH3_ATL _each3.bit._ATL
#define EACH3_EASZ _each3.bitc._EASZ
__IO_EXTENDED EAC4STR _eac4;  
#define EAC4 _eac4.word
#define EAC4_R0 _eac4.bit._R0
#define EAC4_R1 _eac4.bit._R1
#define EAC4_R2 _eac4.bit._R2
#define EAC4_ACE _eac4.bit._ACE
#define EAC4_STS _eac4.bit._STS
#define EAC4_WSF _eac4.bit._WSF
#define EAC4_ES _eac4.bit._ES
#define EAC4_BW _eac4.bit._BW
#define EAC4_EASZ0 _eac4.bit._EASZ0
#define EAC4_EASZ1 _eac4.bit._EASZ1
#define EAC4_EASZ2 _eac4.bit._EASZ2
#define EAC4_CSE _eac4.bit._CSE
#define EAC4_CSL _eac4.bit._CSL
#define EAC4_ATL _eac4.bit._ATL
#define EAC4_R _eac4.bitc._R
#define EAC4_EASZ _eac4.bitc._EASZ
__IO_EXTENDED EACL4STR _eacl4;  
#define EACL4 _eacl4.byte
#define EACL4_R0 _eacl4.bit._R0
#define EACL4_R1 _eacl4.bit._R1
#define EACL4_R2 _eacl4.bit._R2
#define EACL4_ACE _eacl4.bit._ACE
#define EACL4_STS _eacl4.bit._STS
#define EACL4_WSF _eacl4.bit._WSF
#define EACL4_ES _eacl4.bit._ES
#define EACL4_BW _eacl4.bit._BW
#define EACL4_R _eacl4.bitc._R
__IO_EXTENDED EACH4STR _each4;  
#define EACH4 _each4.byte
#define EACH4_EASZ0 _each4.bit._EASZ0
#define EACH4_EASZ1 _each4.bit._EASZ1
#define EACH4_EASZ2 _each4.bit._EASZ2
#define EACH4_CSE _each4.bit._CSE
#define EACH4_CSL _each4.bit._CSL
#define EACH4_ATL _each4.bit._ATL
#define EACH4_EASZ _each4.bitc._EASZ
__IO_EXTENDED EAC5STR _eac5;  
#define EAC5 _eac5.word
#define EAC5_R0 _eac5.bit._R0
#define EAC5_R1 _eac5.bit._R1
#define EAC5_R2 _eac5.bit._R2
#define EAC5_ACE _eac5.bit._ACE
#define EAC5_STS _eac5.bit._STS
#define EAC5_WSF _eac5.bit._WSF
#define EAC5_ES _eac5.bit._ES
#define EAC5_BW _eac5.bit._BW
#define EAC5_EASZ0 _eac5.bit._EASZ0
#define EAC5_EASZ1 _eac5.bit._EASZ1
#define EAC5_EASZ2 _eac5.bit._EASZ2
#define EAC5_CSE _eac5.bit._CSE
#define EAC5_CSL _eac5.bit._CSL
#define EAC5_ATL _eac5.bit._ATL
#define EAC5_R _eac5.bitc._R
#define EAC5_EASZ _eac5.bitc._EASZ
__IO_EXTENDED EACL5STR _eacl5;  
#define EACL5 _eacl5.byte
#define EACL5_R0 _eacl5.bit._R0
#define EACL5_R1 _eacl5.bit._R1
#define EACL5_R2 _eacl5.bit._R2
#define EACL5_ACE _eacl5.bit._ACE
#define EACL5_STS _eacl5.bit._STS
#define EACL5_WSF _eacl5.bit._WSF
#define EACL5_ES _eacl5.bit._ES
#define EACL5_BW _eacl5.bit._BW
#define EACL5_R _eacl5.bitc._R
__IO_EXTENDED EACH5STR _each5;  
#define EACH5 _each5.byte
#define EACH5_EASZ0 _each5.bit._EASZ0
#define EACH5_EASZ1 _each5.bit._EASZ1
#define EACH5_EASZ2 _each5.bit._EASZ2
#define EACH5_CSE _each5.bit._CSE
#define EACH5_CSL _each5.bit._CSL
#define EACH5_ATL _each5.bit._ATL
#define EACH5_EASZ _each5.bitc._EASZ
__IO_EXTENDED EAS2STR _eas2;  
#define EAS2 _eas2.byte
#define EAS2_A0 _eas2.bit._A0
#define EAS2_A1 _eas2.bit._A1
#define EAS2_A2 _eas2.bit._A2
#define EAS2_A3 _eas2.bit._A3
#define EAS2_A4 _eas2.bit._A4
#define EAS2_A5 _eas2.bit._A5
#define EAS2_A6 _eas2.bit._A6
#define EAS2_A7 _eas2.bit._A7
#define EAS2_A _eas2.bitc._A
__IO_EXTENDED EAS3STR _eas3;  
#define EAS3 _eas3.byte
#define EAS3_A0 _eas3.bit._A0
#define EAS3_A1 _eas3.bit._A1
#define EAS3_A2 _eas3.bit._A2
#define EAS3_A3 _eas3.bit._A3
#define EAS3_A4 _eas3.bit._A4
#define EAS3_A5 _eas3.bit._A5
#define EAS3_A6 _eas3.bit._A6
#define EAS3_A7 _eas3.bit._A7
#define EAS3_A _eas3.bitc._A
__IO_EXTENDED EAS4STR _eas4;  
#define EAS4 _eas4.byte
#define EAS4_A0 _eas4.bit._A0
#define EAS4_A1 _eas4.bit._A1
#define EAS4_A2 _eas4.bit._A2
#define EAS4_A3 _eas4.bit._A3
#define EAS4_A4 _eas4.bit._A4
#define EAS4_A5 _eas4.bit._A5
#define EAS4_A6 _eas4.bit._A6
#define EAS4_A7 _eas4.bit._A7
#define EAS4_A _eas4.bitc._A
__IO_EXTENDED EAS5STR _eas5;  
#define EAS5 _eas5.byte
#define EAS5_A0 _eas5.bit._A0
#define EAS5_A1 _eas5.bit._A1
#define EAS5_A2 _eas5.bit._A2
#define EAS5_A3 _eas5.bit._A3
#define EAS5_A4 _eas5.bit._A4
#define EAS5_A5 _eas5.bit._A5
#define EAS5_A6 _eas5.bit._A6
#define EAS5_A7 _eas5.bit._A7
__IO_EXTENDED EBMSTR _ebm;  
#define EBM _ebm.byte
#define EBM_EAE0 _ebm.bit._EAE0
#define EBM_EAE1 _ebm.bit._EAE1
#define EBM_EAE2 _ebm.bit._EAE2
#define EBM_EAE3 _ebm.bit._EAE3
#define EBM_EAE4 _ebm.bit._EAE4
#define EBM_EAE5 _ebm.bit._EAE5
#define EBM_ERE _ebm.bit._ERE
#define EBM_NMS _ebm.bit._NMS
#define EBM_EAE _ebm.bitc._EAE
__IO_EXTENDED EBCFSTR _ebcf;  
#define EBCF _ebcf.byte
#define EBCF_DIV0 _ebcf.bit._DIV0
#define EBCF_DIV1 _ebcf.bit._DIV1
#define EBCF_DIV2 _ebcf.bit._DIV2
#define EBCF_CSM _ebcf.bit._CSM
#define EBCF_CKI _ebcf.bit._CKI
#define EBCF_CKE _ebcf.bit._CKE
#define EBCF_RYE _ebcf.bit._RYE
#define EBCF_HDE _ebcf.bit._HDE
#define EBCF_DIV _ebcf.bitc._DIV
__IO_EXTENDED EBAE0STR _ebae0;  
#define EBAE0 _ebae0.byte
#define EBAE0_A00 _ebae0.bit._A00
#define EBAE0_A01 _ebae0.bit._A01
#define EBAE0_A02 _ebae0.bit._A02
#define EBAE0_A03 _ebae0.bit._A03
#define EBAE0_A04 _ebae0.bit._A04
#define EBAE0_A05 _ebae0.bit._A05
#define EBAE0_A06 _ebae0.bit._A06
#define EBAE0_A07 _ebae0.bit._A07
__IO_EXTENDED EBAE1STR _ebae1;  
#define EBAE1 _ebae1.byte
#define EBAE1_A08 _ebae1.bit._A08
#define EBAE1_A09 _ebae1.bit._A09
#define EBAE1_A10 _ebae1.bit._A10
#define EBAE1_A11 _ebae1.bit._A11
#define EBAE1_A12 _ebae1.bit._A12
#define EBAE1_A13 _ebae1.bit._A13
#define EBAE1_A14 _ebae1.bit._A14
#define EBAE1_A15 _ebae1.bit._A15
__IO_EXTENDED EBAE2STR _ebae2;  
#define EBAE2 _ebae2.byte
#define EBAE2_A16 _ebae2.bit._A16
#define EBAE2_A17 _ebae2.bit._A17
#define EBAE2_A18 _ebae2.bit._A18
#define EBAE2_A19 _ebae2.bit._A19
#define EBAE2_A20 _ebae2.bit._A20
#define EBAE2_A21 _ebae2.bit._A21
#define EBAE2_A22 _ebae2.bit._A22
#define EBAE2_A23 _ebae2.bit._A23
__IO_EXTENDED EBCSSTR _ebcs;  
#define EBCS _ebcs.byte
#define EBCS_LBE _ebcs.bit._LBE
#define EBCS_UBE _ebcs.bit._UBE
#define EBCS_WRLE _ebcs.bit._WRLE
#define EBCS_WRHE _ebcs.bit._WRHE
#define EBCS_RDE _ebcs.bit._RDE
#define EBCS_ASE _ebcs.bit._ASE
#define EBCS_ASL _ebcs.bit._ASL
__IO_EXTENDED CTRLR0STR _ctrlr0;  
#define CTRLR0 _ctrlr0.word
#define CTRLR0_INIT _ctrlr0.bit._INIT
#define CTRLR0_IE _ctrlr0.bit._IE
#define CTRLR0_SIE _ctrlr0.bit._SIE
#define CTRLR0_EIE _ctrlr0.bit._EIE
#define CTRLR0_DAR _ctrlr0.bit._DAR
#define CTRLR0_CCE _ctrlr0.bit._CCE
#define CTRLR0_TEST _ctrlr0.bit._TEST
__IO_EXTENDED CTRLRL0STR _ctrlrl0;  
#define CTRLRL0 _ctrlrl0.byte
#define CTRLRL0_INIT _ctrlrl0.bit._INIT
#define CTRLRL0_IE _ctrlrl0.bit._IE
#define CTRLRL0_SIE _ctrlrl0.bit._SIE
#define CTRLRL0_EIE _ctrlrl0.bit._EIE
#define CTRLRL0_DAR _ctrlrl0.bit._DAR
#define CTRLRL0_CCE _ctrlrl0.bit._CCE
#define CTRLRL0_TEST _ctrlrl0.bit._TEST
__IO_EXTENDED CTRLRH0STR _ctrlrh0;  
#define CTRLRH0 _ctrlrh0.byte
__IO_EXTENDED STATR0STR _statr0;  
#define STATR0 _statr0.word
#define STATR0_LEC0 _statr0.bit._LEC0
#define STATR0_LEC1 _statr0.bit._LEC1
#define STATR0_LEC2 _statr0.bit._LEC2
#define STATR0_TXOK _statr0.bit._TXOK
#define STATR0_RXOK _statr0.bit._RXOK
#define STATR0_EPASS _statr0.bit._EPASS
#define STATR0_EWARN _statr0.bit._EWARN
#define STATR0_BOFF _statr0.bit._BOFF
#define STATR0_LEC _statr0.bitc._LEC
__IO_EXTENDED STATRL0STR _statrl0;  
#define STATRL0 _statrl0.byte
#define STATRL0_LEC0 _statrl0.bit._LEC0
#define STATRL0_LEC1 _statrl0.bit._LEC1
#define STATRL0_LEC2 _statrl0.bit._LEC2
#define STATRL0_TXOK _statrl0.bit._TXOK
#define STATRL0_RXOK _statrl0.bit._RXOK
#define STATRL0_EPASS _statrl0.bit._EPASS
#define STATRL0_EWARN _statrl0.bit._EWARN
#define STATRL0_BOFF _statrl0.bit._BOFF
#define STATRL0_LEC _statrl0.bitc._LEC
__IO_EXTENDED STATRH0STR _statrh0;  
#define STATRH0 _statrh0.byte
__IO_EXTENDED ERRCNT0STR _errcnt0;  
#define ERRCNT0 _errcnt0.word
#define ERRCNT0_TEC0 _errcnt0.bit._TEC0
#define ERRCNT0_TEC1 _errcnt0.bit._TEC1
#define ERRCNT0_TEC2 _errcnt0.bit._TEC2
#define ERRCNT0_TEC3 _errcnt0.bit._TEC3
#define ERRCNT0_TEC4 _errcnt0.bit._TEC4
#define ERRCNT0_TEC5 _errcnt0.bit._TEC5
#define ERRCNT0_TEC6 _errcnt0.bit._TEC6
#define ERRCNT0_TEC7 _errcnt0.bit._TEC7
#define ERRCNT0_REC0 _errcnt0.bit._REC0
#define ERRCNT0_REC1 _errcnt0.bit._REC1
#define ERRCNT0_REC2 _errcnt0.bit._REC2
#define ERRCNT0_REC3 _errcnt0.bit._REC3
#define ERRCNT0_REC4 _errcnt0.bit._REC4
#define ERRCNT0_REC5 _errcnt0.bit._REC5
#define ERRCNT0_REC6 _errcnt0.bit._REC6
#define ERRCNT0_RP _errcnt0.bit._RP
#define ERRCNT0_TEC _errcnt0.bitc._TEC
#define ERRCNT0_REC _errcnt0.bitc._REC
__IO_EXTENDED ERRCNTL0STR _errcntl0;  
#define ERRCNTL0 _errcntl0.byte
#define ERRCNTL0_TEC0 _errcntl0.bit._TEC0
#define ERRCNTL0_TEC1 _errcntl0.bit._TEC1
#define ERRCNTL0_TEC2 _errcntl0.bit._TEC2
#define ERRCNTL0_TEC3 _errcntl0.bit._TEC3
#define ERRCNTL0_TEC4 _errcntl0.bit._TEC4
#define ERRCNTL0_TEC5 _errcntl0.bit._TEC5
#define ERRCNTL0_TEC6 _errcntl0.bit._TEC6
#define ERRCNTL0_TEC7 _errcntl0.bit._TEC7
#define ERRCNTL0_TEC _errcntl0.bitc._TEC
__IO_EXTENDED ERRCNTH0STR _errcnth0;  
#define ERRCNTH0 _errcnth0.byte
#define ERRCNTH0_REC0 _errcnth0.bit._REC0
#define ERRCNTH0_REC1 _errcnth0.bit._REC1
#define ERRCNTH0_REC2 _errcnth0.bit._REC2
#define ERRCNTH0_REC3 _errcnth0.bit._REC3
#define ERRCNTH0_REC4 _errcnth0.bit._REC4
#define ERRCNTH0_REC5 _errcnth0.bit._REC5
#define ERRCNTH0_REC6 _errcnth0.bit._REC6
#define ERRCNTH0_RP _errcnth0.bit._RP
#define ERRCNTH0_REC _errcnth0.bitc._REC
__IO_EXTENDED BTR0STR _btr0;  
#define BTR0 _btr0.word
#define BTR0_BRP0 _btr0.bit._BRP0
#define BTR0_BRP1 _btr0.bit._BRP1
#define BTR0_BRP2 _btr0.bit._BRP2
#define BTR0_BRP3 _btr0.bit._BRP3
#define BTR0_BRP4 _btr0.bit._BRP4
#define BTR0_BRP5 _btr0.bit._BRP5
#define BTR0_SJW0 _btr0.bit._SJW0
#define BTR0_SJW1 _btr0.bit._SJW1
#define BTR0_TSEG10 _btr0.bit._TSEG10
#define BTR0_TSEG11 _btr0.bit._TSEG11
#define BTR0_TSEG12 _btr0.bit._TSEG12
#define BTR0_TSEG13 _btr0.bit._TSEG13
#define BTR0_TSEG20 _btr0.bit._TSEG20
#define BTR0_TSEG21 _btr0.bit._TSEG21
#define BTR0_TSEG22 _btr0.bit._TSEG22
#define BTR0_BRP _btr0.bitc._BRP
#define BTR0_SJW _btr0.bitc._SJW
#define BTR0_TSEG1 _btr0.bitc._TSEG1
#define BTR0_TSEG2 _btr0.bitc._TSEG2
__IO_EXTENDED BTRL0STR _btrl0;  
#define BTRL0 _btrl0.byte
#define BTRL0_BRP0 _btrl0.bit._BRP0
#define BTRL0_BRP1 _btrl0.bit._BRP1
#define BTRL0_BRP2 _btrl0.bit._BRP2
#define BTRL0_BRP3 _btrl0.bit._BRP3
#define BTRL0_BRP4 _btrl0.bit._BRP4
#define BTRL0_BRP5 _btrl0.bit._BRP5
#define BTRL0_SJW0 _btrl0.bit._SJW0
#define BTRL0_SJW1 _btrl0.bit._SJW1
#define BTRL0_BRP _btrl0.bitc._BRP
#define BTRL0_SJW _btrl0.bitc._SJW
__IO_EXTENDED BTRH0STR _btrh0;  
#define BTRH0 _btrh0.byte
#define BTRH0_TSEG10 _btrh0.bit._TSEG10
#define BTRH0_TSEG11 _btrh0.bit._TSEG11
#define BTRH0_TSEG12 _btrh0.bit._TSEG12
#define BTRH0_TSEG13 _btrh0.bit._TSEG13
#define BTRH0_TSEG20 _btrh0.bit._TSEG20
#define BTRH0_TSEG21 _btrh0.bit._TSEG21
#define BTRH0_TSEG22 _btrh0.bit._TSEG22
#define BTRH0_TSEG1 _btrh0.bitc._TSEG1
#define BTRH0_TSEG2 _btrh0.bitc._TSEG2
__IO_EXTENDED INTR0STR _intr0;  
#define INTR0 _intr0.word
#define INTR0_INTID0 _intr0.bit._INTID0
#define INTR0_INTID1 _intr0.bit._INTID1
#define INTR0_INTID2 _intr0.bit._INTID2
#define INTR0_INTID3 _intr0.bit._INTID3
#define INTR0_INTID4 _intr0.bit._INTID4
#define INTR0_INTID5 _intr0.bit._INTID5
#define INTR0_INTID6 _intr0.bit._INTID6
#define INTR0_INTID7 _intr0.bit._INTID7
#define INTR0_INTID8 _intr0.bit._INTID8
#define INTR0_INTID9 _intr0.bit._INTID9
#define INTR0_INTID10 _intr0.bit._INTID10
#define INTR0_INTID11 _intr0.bit._INTID11
#define INTR0_INTID12 _intr0.bit._INTID12
#define INTR0_INTID13 _intr0.bit._INTID13
#define INTR0_INTID14 _intr0.bit._INTID14
#define INTR0_INTID15 _intr0.bit._INTID15
#define INTR0_INTID _intr0.bitc._INTID
__IO_EXTENDED INTRL0STR _intrl0;  
#define INTRL0 _intrl0.byte
#define INTRL0_INTID0 _intrl0.bit._INTID0
#define INTRL0_INTID1 _intrl0.bit._INTID1
#define INTRL0_INTID2 _intrl0.bit._INTID2
#define INTRL0_INTID3 _intrl0.bit._INTID3
#define INTRL0_INTID4 _intrl0.bit._INTID4
#define INTRL0_INTID5 _intrl0.bit._INTID5
#define INTRL0_INTID6 _intrl0.bit._INTID6
#define INTRL0_INTID7 _intrl0.bit._INTID7
__IO_EXTENDED INTRH0STR _intrh0;  
#define INTRH0 _intrh0.byte
#define INTRH0_INTID8 _intrh0.bit._INTID8
#define INTRH0_INTID9 _intrh0.bit._INTID9
#define INTRH0_INTID10 _intrh0.bit._INTID10
#define INTRH0_INTID11 _intrh0.bit._INTID11
#define INTRH0_INTID12 _intrh0.bit._INTID12
#define INTRH0_INTID13 _intrh0.bit._INTID13
#define INTRH0_INTID14 _intrh0.bit._INTID14
#define INTRH0_INTID15 _intrh0.bit._INTID15
__IO_EXTENDED TESTR0STR _testr0;  
#define TESTR0 _testr0.word
#define TESTR0_BASIC _testr0.bit._BASIC
#define TESTR0_SILENT _testr0.bit._SILENT
#define TESTR0_LBACK _testr0.bit._LBACK
#define TESTR0_TX0 _testr0.bit._TX0
#define TESTR0_TX1 _testr0.bit._TX1
#define TESTR0_RX _testr0.bit._RX
__IO_EXTENDED TESTRL0STR _testrl0;  
#define TESTRL0 _testrl0.byte
#define TESTRL0_BASIC _testrl0.bit._BASIC
#define TESTRL0_SILENT _testrl0.bit._SILENT
#define TESTRL0_LBACK _testrl0.bit._LBACK
#define TESTRL0_TX0 _testrl0.bit._TX0
#define TESTRL0_TX1 _testrl0.bit._TX1
#define TESTRL0_RX _testrl0.bit._RX
__IO_EXTENDED TESTRH0STR _testrh0;  
#define TESTRH0 _testrh0.byte
__IO_EXTENDED BRPER0STR _brper0;  
#define BRPER0 _brper0.word
#define BRPER0_BRPE0 _brper0.bit._BRPE0
#define BRPER0_BRPE1 _brper0.bit._BRPE1
#define BRPER0_BRPE2 _brper0.bit._BRPE2
#define BRPER0_BRPE3 _brper0.bit._BRPE3
#define BRPER0_BRPE _brper0.bitc._BRPE
__IO_EXTENDED BRPERL0STR _brperl0;  
#define BRPERL0 _brperl0.byte
#define BRPERL0_BRPE0 _brperl0.bit._BRPE0
#define BRPERL0_BRPE1 _brperl0.bit._BRPE1
#define BRPERL0_BRPE2 _brperl0.bit._BRPE2
#define BRPERL0_BRPE3 _brperl0.bit._BRPE3
#define BRPERL0_BRPE _brperl0.bitc._BRPE
__IO_EXTENDED BRPERH0STR _brperh0;  
#define BRPERH0 _brperh0.byte
__IO_EXTENDED IF1CREQ0STR _if1creq0;  
#define IF1CREQ0 _if1creq0.word
#define IF1CREQ0_MSGN0 _if1creq0.bit._MSGN0
#define IF1CREQ0_MSGN1 _if1creq0.bit._MSGN1
#define IF1CREQ0_MSGN2 _if1creq0.bit._MSGN2
#define IF1CREQ0_MSGN3 _if1creq0.bit._MSGN3
#define IF1CREQ0_MSGN4 _if1creq0.bit._MSGN4
#define IF1CREQ0_MSGN5 _if1creq0.bit._MSGN5
#define IF1CREQ0_MSGN6 _if1creq0.bit._MSGN6
#define IF1CREQ0_MSGN7 _if1creq0.bit._MSGN7
#define IF1CREQ0_BUSY _if1creq0.bit._BUSY
__IO_EXTENDED IF1CREQL0STR _if1creql0;  
#define IF1CREQL0 _if1creql0.byte
#define IF1CREQL0_MSGN0 _if1creql0.bit._MSGN0
#define IF1CREQL0_MSGN1 _if1creql0.bit._MSGN1
#define IF1CREQL0_MSGN2 _if1creql0.bit._MSGN2
#define IF1CREQL0_MSGN3 _if1creql0.bit._MSGN3
#define IF1CREQL0_MSGN4 _if1creql0.bit._MSGN4
#define IF1CREQL0_MSGN5 _if1creql0.bit._MSGN5
#define IF1CREQL0_MSGN6 _if1creql0.bit._MSGN6
#define IF1CREQL0_MSGN7 _if1creql0.bit._MSGN7
__IO_EXTENDED IF1CREQH0STR _if1creqh0;  
#define IF1CREQH0 _if1creqh0.byte
#define IF1CREQH0_BUSY _if1creqh0.bit._BUSY
__IO_EXTENDED IF1CMSK0STR _if1cmsk0;  
#define IF1CMSK0 _if1cmsk0.word
#define IF1CMSK0_DATAB _if1cmsk0.bit._DATAB
#define IF1CMSK0_DATAA _if1cmsk0.bit._DATAA
#define IF1CMSK0_TXREQ _if1cmsk0.bit._TXREQ
#define IF1CMSK0_CIP _if1cmsk0.bit._CIP
#define IF1CMSK0_CONTROL _if1cmsk0.bit._CONTROL
#define IF1CMSK0_ARB _if1cmsk0.bit._ARB
#define IF1CMSK0_MASK _if1cmsk0.bit._MASK
#define IF1CMSK0_WRRD _if1cmsk0.bit._WRRD
__IO_EXTENDED IF1CMSKL0STR _if1cmskl0;  
#define IF1CMSKL0 _if1cmskl0.byte
#define IF1CMSKL0_DATAB _if1cmskl0.bit._DATAB
#define IF1CMSKL0_DATAA _if1cmskl0.bit._DATAA
#define IF1CMSKL0_TXREQ _if1cmskl0.bit._TXREQ
#define IF1CMSKL0_CIP _if1cmskl0.bit._CIP
#define IF1CMSKL0_CONTROL _if1cmskl0.bit._CONTROL
#define IF1CMSKL0_ARB _if1cmskl0.bit._ARB
#define IF1CMSKL0_MASK _if1cmskl0.bit._MASK
#define IF1CMSKL0_WRRD _if1cmskl0.bit._WRRD
__IO_EXTENDED IF1CMSKH0STR _if1cmskh0;  
#define IF1CMSKH0 _if1cmskh0.byte
__IO_EXTENDED IF1MSK0STR _if1msk0;  
#define IF1MSK0 _if1msk0.lword
#define IF1MSK0_MSK0 _if1msk0.bit._MSK0
#define IF1MSK0_MSK1 _if1msk0.bit._MSK1
#define IF1MSK0_MSK2 _if1msk0.bit._MSK2
#define IF1MSK0_MSK3 _if1msk0.bit._MSK3
#define IF1MSK0_MSK4 _if1msk0.bit._MSK4
#define IF1MSK0_MSK5 _if1msk0.bit._MSK5
#define IF1MSK0_MSK6 _if1msk0.bit._MSK6
#define IF1MSK0_MSK7 _if1msk0.bit._MSK7
#define IF1MSK0_MSK8 _if1msk0.bit._MSK8
#define IF1MSK0_MSK9 _if1msk0.bit._MSK9
#define IF1MSK0_MSK10 _if1msk0.bit._MSK10
#define IF1MSK0_MSK11 _if1msk0.bit._MSK11
#define IF1MSK0_MSK12 _if1msk0.bit._MSK12
#define IF1MSK0_MSK13 _if1msk0.bit._MSK13
#define IF1MSK0_MSK14 _if1msk0.bit._MSK14
#define IF1MSK0_MSK15 _if1msk0.bit._MSK15
#define IF1MSK0_MSK16 _if1msk0.bit._MSK16
#define IF1MSK0_MSK17 _if1msk0.bit._MSK17
#define IF1MSK0_MSK18 _if1msk0.bit._MSK18
#define IF1MSK0_MSK19 _if1msk0.bit._MSK19
#define IF1MSK0_MSK20 _if1msk0.bit._MSK20
#define IF1MSK0_MSK21 _if1msk0.bit._MSK21
#define IF1MSK0_MSK22 _if1msk0.bit._MSK22
#define IF1MSK0_MSK23 _if1msk0.bit._MSK23
#define IF1MSK0_MSK24 _if1msk0.bit._MSK24
#define IF1MSK0_MSK25 _if1msk0.bit._MSK25
#define IF1MSK0_MSK26 _if1msk0.bit._MSK26
#define IF1MSK0_MSK27 _if1msk0.bit._MSK27
#define IF1MSK0_MSK28 _if1msk0.bit._MSK28
#define IF1MSK0_MDIR _if1msk0.bit._MDIR
#define IF1MSK0_MXTD _if1msk0.bit._MXTD
#define IF1MSK0_MSK _if1msk0.bitc._MSK
__IO_EXTENDED IF1MSK10STR _if1msk10;  
#define IF1MSK10 _if1msk10.word
#define IF1MSK10_MSK0 _if1msk10.bit._MSK0
#define IF1MSK10_MSK1 _if1msk10.bit._MSK1
#define IF1MSK10_MSK2 _if1msk10.bit._MSK2
#define IF1MSK10_MSK3 _if1msk10.bit._MSK3
#define IF1MSK10_MSK4 _if1msk10.bit._MSK4
#define IF1MSK10_MSK5 _if1msk10.bit._MSK5
#define IF1MSK10_MSK6 _if1msk10.bit._MSK6
#define IF1MSK10_MSK7 _if1msk10.bit._MSK7
#define IF1MSK10_MSK8 _if1msk10.bit._MSK8
#define IF1MSK10_MSK9 _if1msk10.bit._MSK9
#define IF1MSK10_MSK10 _if1msk10.bit._MSK10
#define IF1MSK10_MSK11 _if1msk10.bit._MSK11
#define IF1MSK10_MSK12 _if1msk10.bit._MSK12
#define IF1MSK10_MSK13 _if1msk10.bit._MSK13
#define IF1MSK10_MSK14 _if1msk10.bit._MSK14
#define IF1MSK10_MSK15 _if1msk10.bit._MSK15
__IO_EXTENDED IF1MSK1L0STR _if1msk1l0;  
#define IF1MSK1L0 _if1msk1l0.byte
#define IF1MSK1L0_MSK0 _if1msk1l0.bit._MSK0
#define IF1MSK1L0_MSK1 _if1msk1l0.bit._MSK1
#define IF1MSK1L0_MSK2 _if1msk1l0.bit._MSK2
#define IF1MSK1L0_MSK3 _if1msk1l0.bit._MSK3
#define IF1MSK1L0_MSK4 _if1msk1l0.bit._MSK4
#define IF1MSK1L0_MSK5 _if1msk1l0.bit._MSK5
#define IF1MSK1L0_MSK6 _if1msk1l0.bit._MSK6
#define IF1MSK1L0_MSK7 _if1msk1l0.bit._MSK7
__IO_EXTENDED IF1MSK1H0STR _if1msk1h0;  
#define IF1MSK1H0 _if1msk1h0.byte
#define IF1MSK1H0_MSK8 _if1msk1h0.bit._MSK8
#define IF1MSK1H0_MSK9 _if1msk1h0.bit._MSK9
#define IF1MSK1H0_MSK10 _if1msk1h0.bit._MSK10
#define IF1MSK1H0_MSK11 _if1msk1h0.bit._MSK11
#define IF1MSK1H0_MSK12 _if1msk1h0.bit._MSK12
#define IF1MSK1H0_MSK13 _if1msk1h0.bit._MSK13
#define IF1MSK1H0_MSK14 _if1msk1h0.bit._MSK14
#define IF1MSK1H0_MSK15 _if1msk1h0.bit._MSK15
__IO_EXTENDED IF1MSK20STR _if1msk20;  
#define IF1MSK20 _if1msk20.word
#define IF1MSK20_MSK16 _if1msk20.bit._MSK16
#define IF1MSK20_MSK17 _if1msk20.bit._MSK17
#define IF1MSK20_MSK18 _if1msk20.bit._MSK18
#define IF1MSK20_MSK19 _if1msk20.bit._MSK19
#define IF1MSK20_MSK20 _if1msk20.bit._MSK20
#define IF1MSK20_MSK21 _if1msk20.bit._MSK21
#define IF1MSK20_MSK22 _if1msk20.bit._MSK22
#define IF1MSK20_MSK23 _if1msk20.bit._MSK23
#define IF1MSK20_MSK24 _if1msk20.bit._MSK24
#define IF1MSK20_MSK25 _if1msk20.bit._MSK25
#define IF1MSK20_MSK26 _if1msk20.bit._MSK26
#define IF1MSK20_MSK27 _if1msk20.bit._MSK27
#define IF1MSK20_MSK28 _if1msk20.bit._MSK28
#define IF1MSK20_MDIR _if1msk20.bit._MDIR
#define IF1MSK20_MXTD _if1msk20.bit._MXTD
__IO_EXTENDED IF1MSK2L0STR _if1msk2l0;  
#define IF1MSK2L0 _if1msk2l0.byte
#define IF1MSK2L0_MSK16 _if1msk2l0.bit._MSK16
#define IF1MSK2L0_MSK17 _if1msk2l0.bit._MSK17
#define IF1MSK2L0_MSK18 _if1msk2l0.bit._MSK18
#define IF1MSK2L0_MSK19 _if1msk2l0.bit._MSK19
#define IF1MSK2L0_MSK20 _if1msk2l0.bit._MSK20
#define IF1MSK2L0_MSK21 _if1msk2l0.bit._MSK21
#define IF1MSK2L0_MSK22 _if1msk2l0.bit._MSK22
#define IF1MSK2L0_MSK23 _if1msk2l0.bit._MSK23
__IO_EXTENDED IF1MSK2H0STR _if1msk2h0;  
#define IF1MSK2H0 _if1msk2h0.byte
#define IF1MSK2H0_MSK24 _if1msk2h0.bit._MSK24
#define IF1MSK2H0_MSK25 _if1msk2h0.bit._MSK25
#define IF1MSK2H0_MSK26 _if1msk2h0.bit._MSK26
#define IF1MSK2H0_MSK27 _if1msk2h0.bit._MSK27
#define IF1MSK2H0_MSK28 _if1msk2h0.bit._MSK28
#define IF1MSK2H0_MDIR _if1msk2h0.bit._MDIR
#define IF1MSK2H0_MXTD _if1msk2h0.bit._MXTD
__IO_EXTENDED IF1ARB0STR _if1arb0;  
#define IF1ARB0 _if1arb0.lword
#define IF1ARB0_ID0 _if1arb0.bit._ID0
#define IF1ARB0_ID1 _if1arb0.bit._ID1
#define IF1ARB0_ID2 _if1arb0.bit._ID2
#define IF1ARB0_ID3 _if1arb0.bit._ID3
#define IF1ARB0_ID4 _if1arb0.bit._ID4
#define IF1ARB0_ID5 _if1arb0.bit._ID5
#define IF1ARB0_ID6 _if1arb0.bit._ID6
#define IF1ARB0_ID7 _if1arb0.bit._ID7
#define IF1ARB0_ID8 _if1arb0.bit._ID8
#define IF1ARB0_ID9 _if1arb0.bit._ID9
#define IF1ARB0_ID10 _if1arb0.bit._ID10
#define IF1ARB0_ID11 _if1arb0.bit._ID11
#define IF1ARB0_ID12 _if1arb0.bit._ID12
#define IF1ARB0_ID13 _if1arb0.bit._ID13
#define IF1ARB0_ID14 _if1arb0.bit._ID14
#define IF1ARB0_ID15 _if1arb0.bit._ID15
#define IF1ARB0_ID16 _if1arb0.bit._ID16
#define IF1ARB0_ID17 _if1arb0.bit._ID17
#define IF1ARB0_ID18 _if1arb0.bit._ID18
#define IF1ARB0_ID19 _if1arb0.bit._ID19
#define IF1ARB0_ID20 _if1arb0.bit._ID20
#define IF1ARB0_ID21 _if1arb0.bit._ID21
#define IF1ARB0_ID22 _if1arb0.bit._ID22
#define IF1ARB0_ID23 _if1arb0.bit._ID23
#define IF1ARB0_ID24 _if1arb0.bit._ID24
#define IF1ARB0_ID25 _if1arb0.bit._ID25
#define IF1ARB0_ID26 _if1arb0.bit._ID26
#define IF1ARB0_ID27 _if1arb0.bit._ID27
#define IF1ARB0_ID28 _if1arb0.bit._ID28
#define IF1ARB0_DIR _if1arb0.bit._DIR
#define IF1ARB0_XTD _if1arb0.bit._XTD
#define IF1ARB0_MSGVAL _if1arb0.bit._MSGVAL
#define IF1ARB0_ID _if1arb0.bitc._ID
__IO_EXTENDED IF1ARB10STR _if1arb10;  
#define IF1ARB10 _if1arb10.word
#define IF1ARB10_ID0 _if1arb10.bit._ID0
#define IF1ARB10_ID1 _if1arb10.bit._ID1
#define IF1ARB10_ID2 _if1arb10.bit._ID2
#define IF1ARB10_ID3 _if1arb10.bit._ID3
#define IF1ARB10_ID4 _if1arb10.bit._ID4
#define IF1ARB10_ID5 _if1arb10.bit._ID5
#define IF1ARB10_ID6 _if1arb10.bit._ID6
#define IF1ARB10_ID7 _if1arb10.bit._ID7
#define IF1ARB10_ID8 _if1arb10.bit._ID8
#define IF1ARB10_ID9 _if1arb10.bit._ID9
#define IF1ARB10_ID10 _if1arb10.bit._ID10
#define IF1ARB10_ID11 _if1arb10.bit._ID11
#define IF1ARB10_ID12 _if1arb10.bit._ID12
#define IF1ARB10_ID13 _if1arb10.bit._ID13
#define IF1ARB10_ID14 _if1arb10.bit._ID14
#define IF1ARB10_ID15 _if1arb10.bit._ID15
__IO_EXTENDED IF1ARB1L0STR _if1arb1l0;  
#define IF1ARB1L0 _if1arb1l0.byte
#define IF1ARB1L0_ID0 _if1arb1l0.bit._ID0
#define IF1ARB1L0_ID1 _if1arb1l0.bit._ID1
#define IF1ARB1L0_ID2 _if1arb1l0.bit._ID2
#define IF1ARB1L0_ID3 _if1arb1l0.bit._ID3
#define IF1ARB1L0_ID4 _if1arb1l0.bit._ID4
#define IF1ARB1L0_ID5 _if1arb1l0.bit._ID5
#define IF1ARB1L0_ID6 _if1arb1l0.bit._ID6
#define IF1ARB1L0_ID7 _if1arb1l0.bit._ID7
__IO_EXTENDED IF1ARB1H0STR _if1arb1h0;  
#define IF1ARB1H0 _if1arb1h0.byte
#define IF1ARB1H0_ID8 _if1arb1h0.bit._ID8
#define IF1ARB1H0_ID9 _if1arb1h0.bit._ID9
#define IF1ARB1H0_ID10 _if1arb1h0.bit._ID10
#define IF1ARB1H0_ID11 _if1arb1h0.bit._ID11
#define IF1ARB1H0_ID12 _if1arb1h0.bit._ID12
#define IF1ARB1H0_ID13 _if1arb1h0.bit._ID13
#define IF1ARB1H0_ID14 _if1arb1h0.bit._ID14
#define IF1ARB1H0_ID15 _if1arb1h0.bit._ID15
__IO_EXTENDED IF1ARB20STR _if1arb20;  
#define IF1ARB20 _if1arb20.word
#define IF1ARB20_ID16 _if1arb20.bit._ID16
#define IF1ARB20_ID17 _if1arb20.bit._ID17
#define IF1ARB20_ID18 _if1arb20.bit._ID18
#define IF1ARB20_ID19 _if1arb20.bit._ID19
#define IF1ARB20_ID20 _if1arb20.bit._ID20
#define IF1ARB20_ID21 _if1arb20.bit._ID21
#define IF1ARB20_ID22 _if1arb20.bit._ID22
#define IF1ARB20_ID23 _if1arb20.bit._ID23
#define IF1ARB20_ID24 _if1arb20.bit._ID24
#define IF1ARB20_ID25 _if1arb20.bit._ID25
#define IF1ARB20_ID26 _if1arb20.bit._ID26
#define IF1ARB20_ID27 _if1arb20.bit._ID27
#define IF1ARB20_ID28 _if1arb20.bit._ID28
#define IF1ARB20_DIR _if1arb20.bit._DIR
#define IF1ARB20_XTD _if1arb20.bit._XTD
#define IF1ARB20_MSGVAL _if1arb20.bit._MSGVAL
__IO_EXTENDED IF1ARB2L0STR _if1arb2l0;  
#define IF1ARB2L0 _if1arb2l0.byte
#define IF1ARB2L0_ID16 _if1arb2l0.bit._ID16
#define IF1ARB2L0_ID17 _if1arb2l0.bit._ID17
#define IF1ARB2L0_ID18 _if1arb2l0.bit._ID18
#define IF1ARB2L0_ID19 _if1arb2l0.bit._ID19
#define IF1ARB2L0_ID20 _if1arb2l0.bit._ID20
#define IF1ARB2L0_ID21 _if1arb2l0.bit._ID21
#define IF1ARB2L0_ID22 _if1arb2l0.bit._ID22
#define IF1ARB2L0_ID23 _if1arb2l0.bit._ID23
__IO_EXTENDED IF1ARB2H0STR _if1arb2h0;  
#define IF1ARB2H0 _if1arb2h0.byte
#define IF1ARB2H0_ID24 _if1arb2h0.bit._ID24
#define IF1ARB2H0_ID25 _if1arb2h0.bit._ID25
#define IF1ARB2H0_ID26 _if1arb2h0.bit._ID26
#define IF1ARB2H0_ID27 _if1arb2h0.bit._ID27
#define IF1ARB2H0_ID28 _if1arb2h0.bit._ID28
#define IF1ARB2H0_DIR _if1arb2h0.bit._DIR
#define IF1ARB2H0_XTD _if1arb2h0.bit._XTD
#define IF1ARB2H0_MSGVAL _if1arb2h0.bit._MSGVAL
__IO_EXTENDED IF1MCTR0STR _if1mctr0;  
#define IF1MCTR0 _if1mctr0.word
#define IF1MCTR0_DLC0 _if1mctr0.bit._DLC0
#define IF1MCTR0_DLC1 _if1mctr0.bit._DLC1
#define IF1MCTR0_DLC2 _if1mctr0.bit._DLC2
#define IF1MCTR0_DLC3 _if1mctr0.bit._DLC3
#define IF1MCTR0_EOB _if1mctr0.bit._EOB
#define IF1MCTR0_TXRQST _if1mctr0.bit._TXRQST
#define IF1MCTR0_RMTEN _if1mctr0.bit._RMTEN
#define IF1MCTR0_RXIE _if1mctr0.bit._RXIE
#define IF1MCTR0_TXIE _if1mctr0.bit._TXIE
#define IF1MCTR0_UMASK _if1mctr0.bit._UMASK
#define IF1MCTR0_INTPND _if1mctr0.bit._INTPND
#define IF1MCTR0_MSGLST _if1mctr0.bit._MSGLST
#define IF1MCTR0_NEWDAT _if1mctr0.bit._NEWDAT
#define IF1MCTR0_DLC _if1mctr0.bitc._DLC
__IO_EXTENDED IF1MCTRL0STR _if1mctrl0;  
#define IF1MCTRL0 _if1mctrl0.byte
#define IF1MCTRL0_DLC0 _if1mctrl0.bit._DLC0
#define IF1MCTRL0_DLC1 _if1mctrl0.bit._DLC1
#define IF1MCTRL0_DLC2 _if1mctrl0.bit._DLC2
#define IF1MCTRL0_DLC3 _if1mctrl0.bit._DLC3
#define IF1MCTRL0_EOB _if1mctrl0.bit._EOB
#define IF1MCTRL0_DLC _if1mctrl0.bitc._DLC
__IO_EXTENDED IF1MCTRH0STR _if1mctrh0;  
#define IF1MCTRH0 _if1mctrh0.byte
#define IF1MCTRH0_TXRQST _if1mctrh0.bit._TXRQST
#define IF1MCTRH0_RMTEN _if1mctrh0.bit._RMTEN
#define IF1MCTRH0_RXIE _if1mctrh0.bit._RXIE
#define IF1MCTRH0_TXIE _if1mctrh0.bit._TXIE
#define IF1MCTRH0_UMASK _if1mctrh0.bit._UMASK
#define IF1MCTRH0_INTPND _if1mctrh0.bit._INTPND
#define IF1MCTRH0_MSGLST _if1mctrh0.bit._MSGLST
#define IF1MCTRH0_NEWDAT _if1mctrh0.bit._NEWDAT
__IO_EXTENDED IF1DTA0STR _if1dta0;  
#define IF1DTA0 _if1dta0.lword
__IO_EXTENDED IF1DTA10STR _if1dta10;  
#define IF1DTA10 _if1dta10.word
__IO_EXTENDED IF1DTA1L0STR _if1dta1l0;  
#define IF1DTA1L0 _if1dta1l0.byte
__IO_EXTENDED IF1DTA1H0STR _if1dta1h0;  
#define IF1DTA1H0 _if1dta1h0.byte
__IO_EXTENDED IF1DTA20STR _if1dta20;  
#define IF1DTA20 _if1dta20.word
__IO_EXTENDED IF1DTA2L0STR _if1dta2l0;  
#define IF1DTA2L0 _if1dta2l0.byte
__IO_EXTENDED IF1DTA2H0STR _if1dta2h0;  
#define IF1DTA2H0 _if1dta2h0.byte
__IO_EXTENDED IF1DTB0STR _if1dtb0;  
#define IF1DTB0 _if1dtb0.lword
__IO_EXTENDED IF1DTB10STR _if1dtb10;  
#define IF1DTB10 _if1dtb10.word
__IO_EXTENDED IF1DTB1L0STR _if1dtb1l0;  
#define IF1DTB1L0 _if1dtb1l0.byte
__IO_EXTENDED IF1DTB1H0STR _if1dtb1h0;  
#define IF1DTB1H0 _if1dtb1h0.byte
__IO_EXTENDED IF1DTB20STR _if1dtb20;  
#define IF1DTB20 _if1dtb20.word
__IO_EXTENDED IF1DTB2L0STR _if1dtb2l0;  
#define IF1DTB2L0 _if1dtb2l0.byte
__IO_EXTENDED IF1DTB2H0STR _if1dtb2h0;  
#define IF1DTB2H0 _if1dtb2h0.byte
__IO_EXTENDED IF2CREQ0STR _if2creq0;  
#define IF2CREQ0 _if2creq0.word
#define IF2CREQ0_MSGN0 _if2creq0.bit._MSGN0
#define IF2CREQ0_MSGN1 _if2creq0.bit._MSGN1
#define IF2CREQ0_MSGN2 _if2creq0.bit._MSGN2
#define IF2CREQ0_MSGN3 _if2creq0.bit._MSGN3
#define IF2CREQ0_MSGN4 _if2creq0.bit._MSGN4
#define IF2CREQ0_MSGN5 _if2creq0.bit._MSGN5
#define IF2CREQ0_MSGN6 _if2creq0.bit._MSGN6
#define IF2CREQ0_MSGN7 _if2creq0.bit._MSGN7
#define IF2CREQ0_BUSY _if2creq0.bit._BUSY
__IO_EXTENDED IF2CREQL0STR _if2creql0;  
#define IF2CREQL0 _if2creql0.byte
#define IF2CREQL0_MSGN0 _if2creql0.bit._MSGN0
#define IF2CREQL0_MSGN1 _if2creql0.bit._MSGN1
#define IF2CREQL0_MSGN2 _if2creql0.bit._MSGN2
#define IF2CREQL0_MSGN3 _if2creql0.bit._MSGN3
#define IF2CREQL0_MSGN4 _if2creql0.bit._MSGN4
#define IF2CREQL0_MSGN5 _if2creql0.bit._MSGN5
#define IF2CREQL0_MSGN6 _if2creql0.bit._MSGN6
#define IF2CREQL0_MSGN7 _if2creql0.bit._MSGN7
__IO_EXTENDED IF2CREQH0STR _if2creqh0;  
#define IF2CREQH0 _if2creqh0.byte
#define IF2CREQH0_BUSY _if2creqh0.bit._BUSY
__IO_EXTENDED IF2CMSK0STR _if2cmsk0;  
#define IF2CMSK0 _if2cmsk0.word
#define IF2CMSK0_DATAB _if2cmsk0.bit._DATAB
#define IF2CMSK0_DATAA _if2cmsk0.bit._DATAA
#define IF2CMSK0_TXREQ _if2cmsk0.bit._TXREQ
#define IF2CMSK0_CIP _if2cmsk0.bit._CIP
#define IF2CMSK0_CONTROL _if2cmsk0.bit._CONTROL
#define IF2CMSK0_ARB _if2cmsk0.bit._ARB
#define IF2CMSK0_MASK _if2cmsk0.bit._MASK
#define IF2CMSK0_WRRD _if2cmsk0.bit._WRRD
__IO_EXTENDED IF2CMSKL0STR _if2cmskl0;  
#define IF2CMSKL0 _if2cmskl0.byte
#define IF2CMSKL0_DATAB _if2cmskl0.bit._DATAB
#define IF2CMSKL0_DATAA _if2cmskl0.bit._DATAA
#define IF2CMSKL0_TXREQ _if2cmskl0.bit._TXREQ
#define IF2CMSKL0_CIP _if2cmskl0.bit._CIP
#define IF2CMSKL0_CONTROL _if2cmskl0.bit._CONTROL
#define IF2CMSKL0_ARB _if2cmskl0.bit._ARB
#define IF2CMSKL0_MASK _if2cmskl0.bit._MASK
#define IF2CMSKL0_WRRD _if2cmskl0.bit._WRRD
__IO_EXTENDED IF2CMSKH0STR _if2cmskh0;  
#define IF2CMSKH0 _if2cmskh0.byte
__IO_EXTENDED IF2MSK0STR _if2msk0;  
#define IF2MSK0 _if2msk0.lword
#define IF2MSK0_MSK0 _if2msk0.bit._MSK0
#define IF2MSK0_MSK1 _if2msk0.bit._MSK1
#define IF2MSK0_MSK2 _if2msk0.bit._MSK2
#define IF2MSK0_MSK3 _if2msk0.bit._MSK3
#define IF2MSK0_MSK4 _if2msk0.bit._MSK4
#define IF2MSK0_MSK5 _if2msk0.bit._MSK5
#define IF2MSK0_MSK6 _if2msk0.bit._MSK6
#define IF2MSK0_MSK7 _if2msk0.bit._MSK7
#define IF2MSK0_MSK8 _if2msk0.bit._MSK8
#define IF2MSK0_MSK9 _if2msk0.bit._MSK9
#define IF2MSK0_MSK10 _if2msk0.bit._MSK10
#define IF2MSK0_MSK11 _if2msk0.bit._MSK11
#define IF2MSK0_MSK12 _if2msk0.bit._MSK12
#define IF2MSK0_MSK13 _if2msk0.bit._MSK13
#define IF2MSK0_MSK14 _if2msk0.bit._MSK14
#define IF2MSK0_MSK15 _if2msk0.bit._MSK15
#define IF2MSK0_MSK16 _if2msk0.bit._MSK16
#define IF2MSK0_MSK17 _if2msk0.bit._MSK17
#define IF2MSK0_MSK18 _if2msk0.bit._MSK18
#define IF2MSK0_MSK19 _if2msk0.bit._MSK19
#define IF2MSK0_MSK20 _if2msk0.bit._MSK20
#define IF2MSK0_MSK21 _if2msk0.bit._MSK21
#define IF2MSK0_MSK22 _if2msk0.bit._MSK22
#define IF2MSK0_MSK23 _if2msk0.bit._MSK23
#define IF2MSK0_MSK24 _if2msk0.bit._MSK24
#define IF2MSK0_MSK25 _if2msk0.bit._MSK25
#define IF2MSK0_MSK26 _if2msk0.bit._MSK26
#define IF2MSK0_MSK27 _if2msk0.bit._MSK27
#define IF2MSK0_MSK28 _if2msk0.bit._MSK28
#define IF2MSK0_MDIR _if2msk0.bit._MDIR
#define IF2MSK0_MXTD _if2msk0.bit._MXTD
#define IF2MSK0_MSK _if2msk0.bitc._MSK
__IO_EXTENDED IF2MSK10STR _if2msk10;  
#define IF2MSK10 _if2msk10.word
#define IF2MSK10_MSK0 _if2msk10.bit._MSK0
#define IF2MSK10_MSK1 _if2msk10.bit._MSK1
#define IF2MSK10_MSK2 _if2msk10.bit._MSK2
#define IF2MSK10_MSK3 _if2msk10.bit._MSK3
#define IF2MSK10_MSK4 _if2msk10.bit._MSK4
#define IF2MSK10_MSK5 _if2msk10.bit._MSK5
#define IF2MSK10_MSK6 _if2msk10.bit._MSK6
#define IF2MSK10_MSK7 _if2msk10.bit._MSK7
#define IF2MSK10_MSK8 _if2msk10.bit._MSK8
#define IF2MSK10_MSK9 _if2msk10.bit._MSK9
#define IF2MSK10_MSK10 _if2msk10.bit._MSK10
#define IF2MSK10_MSK11 _if2msk10.bit._MSK11
#define IF2MSK10_MSK12 _if2msk10.bit._MSK12
#define IF2MSK10_MSK13 _if2msk10.bit._MSK13
#define IF2MSK10_MSK14 _if2msk10.bit._MSK14
#define IF2MSK10_MSK15 _if2msk10.bit._MSK15
__IO_EXTENDED IF2MSK1L0STR _if2msk1l0;  
#define IF2MSK1L0 _if2msk1l0.byte
#define IF2MSK1L0_MSK0 _if2msk1l0.bit._MSK0
#define IF2MSK1L0_MSK1 _if2msk1l0.bit._MSK1
#define IF2MSK1L0_MSK2 _if2msk1l0.bit._MSK2
#define IF2MSK1L0_MSK3 _if2msk1l0.bit._MSK3
#define IF2MSK1L0_MSK4 _if2msk1l0.bit._MSK4
#define IF2MSK1L0_MSK5 _if2msk1l0.bit._MSK5
#define IF2MSK1L0_MSK6 _if2msk1l0.bit._MSK6
#define IF2MSK1L0_MSK7 _if2msk1l0.bit._MSK7
__IO_EXTENDED IF2MSK1H0STR _if2msk1h0;  
#define IF2MSK1H0 _if2msk1h0.byte
#define IF2MSK1H0_MSK8 _if2msk1h0.bit._MSK8
#define IF2MSK1H0_MSK9 _if2msk1h0.bit._MSK9
#define IF2MSK1H0_MSK10 _if2msk1h0.bit._MSK10
#define IF2MSK1H0_MSK11 _if2msk1h0.bit._MSK11
#define IF2MSK1H0_MSK12 _if2msk1h0.bit._MSK12
#define IF2MSK1H0_MSK13 _if2msk1h0.bit._MSK13
#define IF2MSK1H0_MSK14 _if2msk1h0.bit._MSK14
#define IF2MSK1H0_MSK15 _if2msk1h0.bit._MSK15
__IO_EXTENDED IF2MSK20STR _if2msk20;  
#define IF2MSK20 _if2msk20.word
#define IF2MSK20_MSK16 _if2msk20.bit._MSK16
#define IF2MSK20_MSK17 _if2msk20.bit._MSK17
#define IF2MSK20_MSK18 _if2msk20.bit._MSK18
#define IF2MSK20_MSK19 _if2msk20.bit._MSK19
#define IF2MSK20_MSK20 _if2msk20.bit._MSK20
#define IF2MSK20_MSK21 _if2msk20.bit._MSK21
#define IF2MSK20_MSK22 _if2msk20.bit._MSK22
#define IF2MSK20_MSK23 _if2msk20.bit._MSK23
#define IF2MSK20_MSK24 _if2msk20.bit._MSK24
#define IF2MSK20_MSK25 _if2msk20.bit._MSK25
#define IF2MSK20_MSK26 _if2msk20.bit._MSK26
#define IF2MSK20_MSK27 _if2msk20.bit._MSK27
#define IF2MSK20_MSK28 _if2msk20.bit._MSK28
#define IF2MSK20_MDIR _if2msk20.bit._MDIR
#define IF2MSK20_MXTD _if2msk20.bit._MXTD
__IO_EXTENDED IF2MSK2L0STR _if2msk2l0;  
#define IF2MSK2L0 _if2msk2l0.byte
#define IF2MSK2L0_MSK16 _if2msk2l0.bit._MSK16
#define IF2MSK2L0_MSK17 _if2msk2l0.bit._MSK17
#define IF2MSK2L0_MSK18 _if2msk2l0.bit._MSK18
#define IF2MSK2L0_MSK19 _if2msk2l0.bit._MSK19
#define IF2MSK2L0_MSK20 _if2msk2l0.bit._MSK20
#define IF2MSK2L0_MSK21 _if2msk2l0.bit._MSK21
#define IF2MSK2L0_MSK22 _if2msk2l0.bit._MSK22
#define IF2MSK2L0_MSK23 _if2msk2l0.bit._MSK23
__IO_EXTENDED IF2MSK2H0STR _if2msk2h0;  
#define IF2MSK2H0 _if2msk2h0.byte
#define IF2MSK2H0_MSK24 _if2msk2h0.bit._MSK24
#define IF2MSK2H0_MSK25 _if2msk2h0.bit._MSK25
#define IF2MSK2H0_MSK26 _if2msk2h0.bit._MSK26
#define IF2MSK2H0_MSK27 _if2msk2h0.bit._MSK27
#define IF2MSK2H0_MSK28 _if2msk2h0.bit._MSK28
#define IF2MSK2H0_MDIR _if2msk2h0.bit._MDIR
#define IF2MSK2H0_MXTD _if2msk2h0.bit._MXTD
__IO_EXTENDED IF2ARB0STR _if2arb0;  
#define IF2ARB0 _if2arb0.lword
#define IF2ARB0_ID0 _if2arb0.bit._ID0
#define IF2ARB0_ID1 _if2arb0.bit._ID1
#define IF2ARB0_ID2 _if2arb0.bit._ID2
#define IF2ARB0_ID3 _if2arb0.bit._ID3
#define IF2ARB0_ID4 _if2arb0.bit._ID4
#define IF2ARB0_ID5 _if2arb0.bit._ID5
#define IF2ARB0_ID6 _if2arb0.bit._ID6
#define IF2ARB0_ID7 _if2arb0.bit._ID7
#define IF2ARB0_ID8 _if2arb0.bit._ID8
#define IF2ARB0_ID9 _if2arb0.bit._ID9
#define IF2ARB0_ID10 _if2arb0.bit._ID10
#define IF2ARB0_ID11 _if2arb0.bit._ID11
#define IF2ARB0_ID12 _if2arb0.bit._ID12
#define IF2ARB0_ID13 _if2arb0.bit._ID13
#define IF2ARB0_ID14 _if2arb0.bit._ID14
#define IF2ARB0_ID15 _if2arb0.bit._ID15
#define IF2ARB0_ID16 _if2arb0.bit._ID16
#define IF2ARB0_ID17 _if2arb0.bit._ID17
#define IF2ARB0_ID18 _if2arb0.bit._ID18
#define IF2ARB0_ID19 _if2arb0.bit._ID19
#define IF2ARB0_ID20 _if2arb0.bit._ID20
#define IF2ARB0_ID21 _if2arb0.bit._ID21
#define IF2ARB0_ID22 _if2arb0.bit._ID22
#define IF2ARB0_ID23 _if2arb0.bit._ID23
#define IF2ARB0_ID24 _if2arb0.bit._ID24
#define IF2ARB0_ID25 _if2arb0.bit._ID25
#define IF2ARB0_ID26 _if2arb0.bit._ID26
#define IF2ARB0_ID27 _if2arb0.bit._ID27
#define IF2ARB0_ID28 _if2arb0.bit._ID28
#define IF2ARB0_DIR _if2arb0.bit._DIR
#define IF2ARB0_XTD _if2arb0.bit._XTD
#define IF2ARB0_MSGVAL _if2arb0.bit._MSGVAL
#define IF2ARB0_ID _if2arb0.bitc._ID
__IO_EXTENDED IF2ARB10STR _if2arb10;  
#define IF2ARB10 _if2arb10.word
#define IF2ARB10_ID0 _if2arb10.bit._ID0
#define IF2ARB10_ID1 _if2arb10.bit._ID1
#define IF2ARB10_ID2 _if2arb10.bit._ID2
#define IF2ARB10_ID3 _if2arb10.bit._ID3
#define IF2ARB10_ID4 _if2arb10.bit._ID4
#define IF2ARB10_ID5 _if2arb10.bit._ID5
#define IF2ARB10_ID6 _if2arb10.bit._ID6
#define IF2ARB10_ID7 _if2arb10.bit._ID7
#define IF2ARB10_ID8 _if2arb10.bit._ID8
#define IF2ARB10_ID9 _if2arb10.bit._ID9
#define IF2ARB10_ID10 _if2arb10.bit._ID10
#define IF2ARB10_ID11 _if2arb10.bit._ID11
#define IF2ARB10_ID12 _if2arb10.bit._ID12
#define IF2ARB10_ID13 _if2arb10.bit._ID13
#define IF2ARB10_ID14 _if2arb10.bit._ID14
#define IF2ARB10_ID15 _if2arb10.bit._ID15
__IO_EXTENDED IF2ARB1L0STR _if2arb1l0;  
#define IF2ARB1L0 _if2arb1l0.byte
#define IF2ARB1L0_ID0 _if2arb1l0.bit._ID0
#define IF2ARB1L0_ID1 _if2arb1l0.bit._ID1
#define IF2ARB1L0_ID2 _if2arb1l0.bit._ID2
#define IF2ARB1L0_ID3 _if2arb1l0.bit._ID3
#define IF2ARB1L0_ID4 _if2arb1l0.bit._ID4
#define IF2ARB1L0_ID5 _if2arb1l0.bit._ID5
#define IF2ARB1L0_ID6 _if2arb1l0.bit._ID6
#define IF2ARB1L0_ID7 _if2arb1l0.bit._ID7
__IO_EXTENDED IF2ARB1H0STR _if2arb1h0;  
#define IF2ARB1H0 _if2arb1h0.byte
#define IF2ARB1H0_ID8 _if2arb1h0.bit._ID8
#define IF2ARB1H0_ID9 _if2arb1h0.bit._ID9
#define IF2ARB1H0_ID10 _if2arb1h0.bit._ID10
#define IF2ARB1H0_ID11 _if2arb1h0.bit._ID11
#define IF2ARB1H0_ID12 _if2arb1h0.bit._ID12
#define IF2ARB1H0_ID13 _if2arb1h0.bit._ID13
#define IF2ARB1H0_ID14 _if2arb1h0.bit._ID14
#define IF2ARB1H0_ID15 _if2arb1h0.bit._ID15
__IO_EXTENDED IF2ARB20STR _if2arb20;  
#define IF2ARB20 _if2arb20.word
#define IF2ARB20_ID16 _if2arb20.bit._ID16
#define IF2ARB20_ID17 _if2arb20.bit._ID17
#define IF2ARB20_ID18 _if2arb20.bit._ID18
#define IF2ARB20_ID19 _if2arb20.bit._ID19
#define IF2ARB20_ID20 _if2arb20.bit._ID20
#define IF2ARB20_ID21 _if2arb20.bit._ID21
#define IF2ARB20_ID22 _if2arb20.bit._ID22
#define IF2ARB20_ID23 _if2arb20.bit._ID23
#define IF2ARB20_ID24 _if2arb20.bit._ID24
#define IF2ARB20_ID25 _if2arb20.bit._ID25
#define IF2ARB20_ID26 _if2arb20.bit._ID26
#define IF2ARB20_ID27 _if2arb20.bit._ID27
#define IF2ARB20_ID28 _if2arb20.bit._ID28
#define IF2ARB20_DIR _if2arb20.bit._DIR
#define IF2ARB20_XTD _if2arb20.bit._XTD
#define IF2ARB20_MSGVAL _if2arb20.bit._MSGVAL
__IO_EXTENDED IF2ARB2L0STR _if2arb2l0;  
#define IF2ARB2L0 _if2arb2l0.byte
#define IF2ARB2L0_ID16 _if2arb2l0.bit._ID16
#define IF2ARB2L0_ID17 _if2arb2l0.bit._ID17
#define IF2ARB2L0_ID18 _if2arb2l0.bit._ID18
#define IF2ARB2L0_ID19 _if2arb2l0.bit._ID19
#define IF2ARB2L0_ID20 _if2arb2l0.bit._ID20
#define IF2ARB2L0_ID21 _if2arb2l0.bit._ID21
#define IF2ARB2L0_ID22 _if2arb2l0.bit._ID22
#define IF2ARB2L0_ID23 _if2arb2l0.bit._ID23
__IO_EXTENDED IF2ARB2H0STR _if2arb2h0;  
#define IF2ARB2H0 _if2arb2h0.byte
#define IF2ARB2H0_ID24 _if2arb2h0.bit._ID24
#define IF2ARB2H0_ID25 _if2arb2h0.bit._ID25
#define IF2ARB2H0_ID26 _if2arb2h0.bit._ID26
#define IF2ARB2H0_ID27 _if2arb2h0.bit._ID27
#define IF2ARB2H0_ID28 _if2arb2h0.bit._ID28
#define IF2ARB2H0_DIR _if2arb2h0.bit._DIR
#define IF2ARB2H0_XTD _if2arb2h0.bit._XTD
#define IF2ARB2H0_MSGVAL _if2arb2h0.bit._MSGVAL
__IO_EXTENDED IF2MCTR0STR _if2mctr0;  
#define IF2MCTR0 _if2mctr0.word
#define IF2MCTR0_DLC0 _if2mctr0.bit._DLC0
#define IF2MCTR0_DLC1 _if2mctr0.bit._DLC1
#define IF2MCTR0_DLC2 _if2mctr0.bit._DLC2
#define IF2MCTR0_DLC3 _if2mctr0.bit._DLC3
#define IF2MCTR0_EOB _if2mctr0.bit._EOB
#define IF2MCTR0_TXRQST _if2mctr0.bit._TXRQST
#define IF2MCTR0_RMTEN _if2mctr0.bit._RMTEN
#define IF2MCTR0_RXIE _if2mctr0.bit._RXIE
#define IF2MCTR0_TXIE _if2mctr0.bit._TXIE
#define IF2MCTR0_UMASK _if2mctr0.bit._UMASK
#define IF2MCTR0_INTPND _if2mctr0.bit._INTPND
#define IF2MCTR0_MSGLST _if2mctr0.bit._MSGLST
#define IF2MCTR0_NEWDAT _if2mctr0.bit._NEWDAT
#define IF2MCTR0_DLC _if2mctr0.bitc._DLC
__IO_EXTENDED IF2MCTRL0STR _if2mctrl0;  
#define IF2MCTRL0 _if2mctrl0.byte
#define IF2MCTRL0_DLC0 _if2mctrl0.bit._DLC0
#define IF2MCTRL0_DLC1 _if2mctrl0.bit._DLC1
#define IF2MCTRL0_DLC2 _if2mctrl0.bit._DLC2
#define IF2MCTRL0_DLC3 _if2mctrl0.bit._DLC3
#define IF2MCTRL0_EOB _if2mctrl0.bit._EOB
#define IF2MCTRL0_DLC _if2mctrl0.bitc._DLC
__IO_EXTENDED IF2MCTRH0STR _if2mctrh0;  
#define IF2MCTRH0 _if2mctrh0.byte
#define IF2MCTRH0_TXRQST _if2mctrh0.bit._TXRQST
#define IF2MCTRH0_RMTEN _if2mctrh0.bit._RMTEN
#define IF2MCTRH0_RXIE _if2mctrh0.bit._RXIE
#define IF2MCTRH0_TXIE _if2mctrh0.bit._TXIE
#define IF2MCTRH0_UMASK _if2mctrh0.bit._UMASK
#define IF2MCTRH0_INTPND _if2mctrh0.bit._INTPND
#define IF2MCTRH0_MSGLST _if2mctrh0.bit._MSGLST
#define IF2MCTRH0_NEWDAT _if2mctrh0.bit._NEWDAT
__IO_EXTENDED IF2DTA0STR _if2dta0;  
#define IF2DTA0 _if2dta0.lword
__IO_EXTENDED IF2DTA10STR _if2dta10;  
#define IF2DTA10 _if2dta10.word
__IO_EXTENDED IF2DTA1L0STR _if2dta1l0;  
#define IF2DTA1L0 _if2dta1l0.byte
__IO_EXTENDED IF2DTA1H0STR _if2dta1h0;  
#define IF2DTA1H0 _if2dta1h0.byte
__IO_EXTENDED IF2DTA20STR _if2dta20;  
#define IF2DTA20 _if2dta20.word
__IO_EXTENDED IF2DTA2L0STR _if2dta2l0;  
#define IF2DTA2L0 _if2dta2l0.byte
__IO_EXTENDED IF2DTA2H0STR _if2dta2h0;  
#define IF2DTA2H0 _if2dta2h0.byte
__IO_EXTENDED IF2DTB0STR _if2dtb0;  
#define IF2DTB0 _if2dtb0.lword
__IO_EXTENDED IF2DTB10STR _if2dtb10;  
#define IF2DTB10 _if2dtb10.word
__IO_EXTENDED IF2DTB1L0STR _if2dtb1l0;  
#define IF2DTB1L0 _if2dtb1l0.byte
__IO_EXTENDED IF2DTB1H0STR _if2dtb1h0;  
#define IF2DTB1H0 _if2dtb1h0.byte
__IO_EXTENDED IF2DTB20STR _if2dtb20;  
#define IF2DTB20 _if2dtb20.word
__IO_EXTENDED IF2DTB2L0STR _if2dtb2l0;  
#define IF2DTB2L0 _if2dtb2l0.byte
__IO_EXTENDED IF2DTB2H0STR _if2dtb2h0;  
#define IF2DTB2H0 _if2dtb2h0.byte
__IO_EXTENDED TREQR0STR _treqr0;  
#define TREQR0 _treqr0.lword
#define TREQR0_TXRQST1 _treqr0.bit._TXRQST1
#define TREQR0_TXRQST2 _treqr0.bit._TXRQST2
#define TREQR0_TXRQST3 _treqr0.bit._TXRQST3
#define TREQR0_TXRQST4 _treqr0.bit._TXRQST4
#define TREQR0_TXRQST5 _treqr0.bit._TXRQST5
#define TREQR0_TXRQST6 _treqr0.bit._TXRQST6
#define TREQR0_TXRQST7 _treqr0.bit._TXRQST7
#define TREQR0_TXRQST8 _treqr0.bit._TXRQST8
#define TREQR0_TXRQST9 _treqr0.bit._TXRQST9
#define TREQR0_TXRQST10 _treqr0.bit._TXRQST10
#define TREQR0_TXRQST11 _treqr0.bit._TXRQST11
#define TREQR0_TXRQST12 _treqr0.bit._TXRQST12
#define TREQR0_TXRQST13 _treqr0.bit._TXRQST13
#define TREQR0_TXRQST14 _treqr0.bit._TXRQST14
#define TREQR0_TXRQST15 _treqr0.bit._TXRQST15
#define TREQR0_TXRQST16 _treqr0.bit._TXRQST16
#define TREQR0_TXRQST17 _treqr0.bit._TXRQST17
#define TREQR0_TXRQST18 _treqr0.bit._TXRQST18
#define TREQR0_TXRQST19 _treqr0.bit._TXRQST19
#define TREQR0_TXRQST20 _treqr0.bit._TXRQST20
#define TREQR0_TXRQST21 _treqr0.bit._TXRQST21
#define TREQR0_TXRQST22 _treqr0.bit._TXRQST22
#define TREQR0_TXRQST23 _treqr0.bit._TXRQST23
#define TREQR0_TXRQST24 _treqr0.bit._TXRQST24
#define TREQR0_TXRQST25 _treqr0.bit._TXRQST25
#define TREQR0_TXRQST26 _treqr0.bit._TXRQST26
#define TREQR0_TXRQST27 _treqr0.bit._TXRQST27
#define TREQR0_TXRQST28 _treqr0.bit._TXRQST28
#define TREQR0_TXRQST29 _treqr0.bit._TXRQST29
#define TREQR0_TXRQST30 _treqr0.bit._TXRQST30
#define TREQR0_TXRQST31 _treqr0.bit._TXRQST31
#define TREQR0_TXRQST32 _treqr0.bit._TXRQST32
#define TREQR0_TXRQST _treqr0.bitc._TXRQST
__IO_EXTENDED TREQR10STR _treqr10;  
#define TREQR10 _treqr10.word
#define TREQR10_TXRQST1 _treqr10.bit._TXRQST1
#define TREQR10_TXRQST2 _treqr10.bit._TXRQST2
#define TREQR10_TXRQST3 _treqr10.bit._TXRQST3
#define TREQR10_TXRQST4 _treqr10.bit._TXRQST4
#define TREQR10_TXRQST5 _treqr10.bit._TXRQST5
#define TREQR10_TXRQST6 _treqr10.bit._TXRQST6
#define TREQR10_TXRQST7 _treqr10.bit._TXRQST7
#define TREQR10_TXRQST8 _treqr10.bit._TXRQST8
#define TREQR10_TXRQST9 _treqr10.bit._TXRQST9
#define TREQR10_TXRQST10 _treqr10.bit._TXRQST10
#define TREQR10_TXRQST11 _treqr10.bit._TXRQST11
#define TREQR10_TXRQST12 _treqr10.bit._TXRQST12
#define TREQR10_TXRQST13 _treqr10.bit._TXRQST13
#define TREQR10_TXRQST14 _treqr10.bit._TXRQST14
#define TREQR10_TXRQST15 _treqr10.bit._TXRQST15
#define TREQR10_TXRQST16 _treqr10.bit._TXRQST16
__IO_EXTENDED TREQR1L0STR _treqr1l0;  
#define TREQR1L0 _treqr1l0.byte
#define TREQR1L0_TXRQST1 _treqr1l0.bit._TXRQST1
#define TREQR1L0_TXRQST2 _treqr1l0.bit._TXRQST2
#define TREQR1L0_TXRQST3 _treqr1l0.bit._TXRQST3
#define TREQR1L0_TXRQST4 _treqr1l0.bit._TXRQST4
#define TREQR1L0_TXRQST5 _treqr1l0.bit._TXRQST5
#define TREQR1L0_TXRQST6 _treqr1l0.bit._TXRQST6
#define TREQR1L0_TXRQST7 _treqr1l0.bit._TXRQST7
#define TREQR1L0_TXRQST8 _treqr1l0.bit._TXRQST8
__IO_EXTENDED TREQR1H0STR _treqr1h0;  
#define TREQR1H0 _treqr1h0.byte
#define TREQR1H0_TXRQST9 _treqr1h0.bit._TXRQST9
#define TREQR1H0_TXRQST10 _treqr1h0.bit._TXRQST10
#define TREQR1H0_TXRQST11 _treqr1h0.bit._TXRQST11
#define TREQR1H0_TXRQST12 _treqr1h0.bit._TXRQST12
#define TREQR1H0_TXRQST13 _treqr1h0.bit._TXRQST13
#define TREQR1H0_TXRQST14 _treqr1h0.bit._TXRQST14
#define TREQR1H0_TXRQST15 _treqr1h0.bit._TXRQST15
#define TREQR1H0_TXRQST16 _treqr1h0.bit._TXRQST16
__IO_EXTENDED TREQR20STR _treqr20;  
#define TREQR20 _treqr20.word
#define TREQR20_TXRQST17 _treqr20.bit._TXRQST17
#define TREQR20_TXRQST18 _treqr20.bit._TXRQST18
#define TREQR20_TXRQST19 _treqr20.bit._TXRQST19
#define TREQR20_TXRQST20 _treqr20.bit._TXRQST20
#define TREQR20_TXRQST21 _treqr20.bit._TXRQST21
#define TREQR20_TXRQST22 _treqr20.bit._TXRQST22
#define TREQR20_TXRQST23 _treqr20.bit._TXRQST23
#define TREQR20_TXRQST24 _treqr20.bit._TXRQST24
#define TREQR20_TXRQST25 _treqr20.bit._TXRQST25
#define TREQR20_TXRQST26 _treqr20.bit._TXRQST26
#define TREQR20_TXRQST27 _treqr20.bit._TXRQST27
#define TREQR20_TXRQST28 _treqr20.bit._TXRQST28
#define TREQR20_TXRQST29 _treqr20.bit._TXRQST29
#define TREQR20_TXRQST30 _treqr20.bit._TXRQST30
#define TREQR20_TXRQST31 _treqr20.bit._TXRQST31
#define TREQR20_TXRQST32 _treqr20.bit._TXRQST32
__IO_EXTENDED TREQR2L0STR _treqr2l0;  
#define TREQR2L0 _treqr2l0.byte
#define TREQR2L0_TXRQST17 _treqr2l0.bit._TXRQST17
#define TREQR2L0_TXRQST18 _treqr2l0.bit._TXRQST18
#define TREQR2L0_TXRQST19 _treqr2l0.bit._TXRQST19
#define TREQR2L0_TXRQST20 _treqr2l0.bit._TXRQST20
#define TREQR2L0_TXRQST21 _treqr2l0.bit._TXRQST21
#define TREQR2L0_TXRQST22 _treqr2l0.bit._TXRQST22
#define TREQR2L0_TXRQST23 _treqr2l0.bit._TXRQST23
#define TREQR2L0_TXRQST24 _treqr2l0.bit._TXRQST24
__IO_EXTENDED TREQR2H0STR _treqr2h0;  
#define TREQR2H0 _treqr2h0.byte
#define TREQR2H0_TXRQST25 _treqr2h0.bit._TXRQST25
#define TREQR2H0_TXRQST26 _treqr2h0.bit._TXRQST26
#define TREQR2H0_TXRQST27 _treqr2h0.bit._TXRQST27
#define TREQR2H0_TXRQST28 _treqr2h0.bit._TXRQST28
#define TREQR2H0_TXRQST29 _treqr2h0.bit._TXRQST29
#define TREQR2H0_TXRQST30 _treqr2h0.bit._TXRQST30
#define TREQR2H0_TXRQST31 _treqr2h0.bit._TXRQST31
#define TREQR2H0_TXRQST32 _treqr2h0.bit._TXRQST32
__IO_EXTENDED NEWDT0STR _newdt0;  
#define NEWDT0 _newdt0.lword
#define NEWDT0_NEWDAT1 _newdt0.bit._NEWDAT1
#define NEWDT0_NEWDAT2 _newdt0.bit._NEWDAT2
#define NEWDT0_NEWDAT3 _newdt0.bit._NEWDAT3
#define NEWDT0_NEWDAT4 _newdt0.bit._NEWDAT4
#define NEWDT0_NEWDAT5 _newdt0.bit._NEWDAT5
#define NEWDT0_NEWDAT6 _newdt0.bit._NEWDAT6
#define NEWDT0_NEWDAT7 _newdt0.bit._NEWDAT7
#define NEWDT0_NEWDAT8 _newdt0.bit._NEWDAT8
#define NEWDT0_NEWDAT9 _newdt0.bit._NEWDAT9
#define NEWDT0_NEWDAT10 _newdt0.bit._NEWDAT10
#define NEWDT0_NEWDAT11 _newdt0.bit._NEWDAT11
#define NEWDT0_NEWDAT12 _newdt0.bit._NEWDAT12
#define NEWDT0_NEWDAT13 _newdt0.bit._NEWDAT13
#define NEWDT0_NEWDAT14 _newdt0.bit._NEWDAT14
#define NEWDT0_NEWDAT15 _newdt0.bit._NEWDAT15
#define NEWDT0_NEWDAT16 _newdt0.bit._NEWDAT16
#define NEWDT0_NEWDAT17 _newdt0.bit._NEWDAT17
#define NEWDT0_NEWDAT18 _newdt0.bit._NEWDAT18
#define NEWDT0_NEWDAT19 _newdt0.bit._NEWDAT19
#define NEWDT0_NEWDAT20 _newdt0.bit._NEWDAT20
#define NEWDT0_NEWDAT21 _newdt0.bit._NEWDAT21
#define NEWDT0_NEWDAT22 _newdt0.bit._NEWDAT22
#define NEWDT0_NEWDAT23 _newdt0.bit._NEWDAT23
#define NEWDT0_NEWDAT24 _newdt0.bit._NEWDAT24
#define NEWDT0_NEWDAT25 _newdt0.bit._NEWDAT25
#define NEWDT0_NEWDAT26 _newdt0.bit._NEWDAT26
#define NEWDT0_NEWDAT27 _newdt0.bit._NEWDAT27
#define NEWDT0_NEWDAT28 _newdt0.bit._NEWDAT28
#define NEWDT0_NEWDAT29 _newdt0.bit._NEWDAT29
#define NEWDT0_NEWDAT30 _newdt0.bit._NEWDAT30
#define NEWDT0_NEWDAT31 _newdt0.bit._NEWDAT31
#define NEWDT0_NEWDAT32 _newdt0.bit._NEWDAT32
#define NEWDT0_NEWDAT _newdt0.bitc._NEWDAT
__IO_EXTENDED NEWDT10STR _newdt10;  
#define NEWDT10 _newdt10.word
#define NEWDT10_NEWDAT1 _newdt10.bit._NEWDAT1
#define NEWDT10_NEWDAT2 _newdt10.bit._NEWDAT2
#define NEWDT10_NEWDAT3 _newdt10.bit._NEWDAT3
#define NEWDT10_NEWDAT4 _newdt10.bit._NEWDAT4
#define NEWDT10_NEWDAT5 _newdt10.bit._NEWDAT5
#define NEWDT10_NEWDAT6 _newdt10.bit._NEWDAT6
#define NEWDT10_NEWDAT7 _newdt10.bit._NEWDAT7
#define NEWDT10_NEWDAT8 _newdt10.bit._NEWDAT8
#define NEWDT10_NEWDAT9 _newdt10.bit._NEWDAT9
#define NEWDT10_NEWDAT10 _newdt10.bit._NEWDAT10
#define NEWDT10_NEWDAT11 _newdt10.bit._NEWDAT11
#define NEWDT10_NEWDAT12 _newdt10.bit._NEWDAT12
#define NEWDT10_NEWDAT13 _newdt10.bit._NEWDAT13
#define NEWDT10_NEWDAT14 _newdt10.bit._NEWDAT14
#define NEWDT10_NEWDAT15 _newdt10.bit._NEWDAT15
#define NEWDT10_NEWDAT16 _newdt10.bit._NEWDAT16
__IO_EXTENDED NEWDT1L0STR _newdt1l0;  
#define NEWDT1L0 _newdt1l0.byte
#define NEWDT1L0_NEWDAT1 _newdt1l0.bit._NEWDAT1
#define NEWDT1L0_NEWDAT2 _newdt1l0.bit._NEWDAT2
#define NEWDT1L0_NEWDAT3 _newdt1l0.bit._NEWDAT3
#define NEWDT1L0_NEWDAT4 _newdt1l0.bit._NEWDAT4
#define NEWDT1L0_NEWDAT5 _newdt1l0.bit._NEWDAT5
#define NEWDT1L0_NEWDAT6 _newdt1l0.bit._NEWDAT6
#define NEWDT1L0_NEWDAT7 _newdt1l0.bit._NEWDAT7
#define NEWDT1L0_NEWDAT8 _newdt1l0.bit._NEWDAT8
__IO_EXTENDED NEWDT1H0STR _newdt1h0;  
#define NEWDT1H0 _newdt1h0.byte
#define NEWDT1H0_NEWDAT9 _newdt1h0.bit._NEWDAT9
#define NEWDT1H0_NEWDAT10 _newdt1h0.bit._NEWDAT10
#define NEWDT1H0_NEWDAT11 _newdt1h0.bit._NEWDAT11
#define NEWDT1H0_NEWDAT12 _newdt1h0.bit._NEWDAT12
#define NEWDT1H0_NEWDAT13 _newdt1h0.bit._NEWDAT13
#define NEWDT1H0_NEWDAT14 _newdt1h0.bit._NEWDAT14
#define NEWDT1H0_NEWDAT15 _newdt1h0.bit._NEWDAT15
#define NEWDT1H0_NEWDAT16 _newdt1h0.bit._NEWDAT16
__IO_EXTENDED NEWDT20STR _newdt20;  
#define NEWDT20 _newdt20.word
#define NEWDT20_NEWDAT17 _newdt20.bit._NEWDAT17
#define NEWDT20_NEWDAT18 _newdt20.bit._NEWDAT18
#define NEWDT20_NEWDAT19 _newdt20.bit._NEWDAT19
#define NEWDT20_NEWDAT20 _newdt20.bit._NEWDAT20
#define NEWDT20_NEWDAT21 _newdt20.bit._NEWDAT21
#define NEWDT20_NEWDAT22 _newdt20.bit._NEWDAT22
#define NEWDT20_NEWDAT23 _newdt20.bit._NEWDAT23
#define NEWDT20_NEWDAT24 _newdt20.bit._NEWDAT24
#define NEWDT20_NEWDAT25 _newdt20.bit._NEWDAT25
#define NEWDT20_NEWDAT26 _newdt20.bit._NEWDAT26
#define NEWDT20_NEWDAT27 _newdt20.bit._NEWDAT27
#define NEWDT20_NEWDAT28 _newdt20.bit._NEWDAT28
#define NEWDT20_NEWDAT29 _newdt20.bit._NEWDAT29
#define NEWDT20_NEWDAT30 _newdt20.bit._NEWDAT30
#define NEWDT20_NEWDAT31 _newdt20.bit._NEWDAT31
#define NEWDT20_NEWDAT32 _newdt20.bit._NEWDAT32
__IO_EXTENDED NEWDT2L0STR _newdt2l0;  
#define NEWDT2L0 _newdt2l0.byte
#define NEWDT2L0_NEWDAT17 _newdt2l0.bit._NEWDAT17
#define NEWDT2L0_NEWDAT18 _newdt2l0.bit._NEWDAT18
#define NEWDT2L0_NEWDAT19 _newdt2l0.bit._NEWDAT19
#define NEWDT2L0_NEWDAT20 _newdt2l0.bit._NEWDAT20
#define NEWDT2L0_NEWDAT21 _newdt2l0.bit._NEWDAT21
#define NEWDT2L0_NEWDAT22 _newdt2l0.bit._NEWDAT22
#define NEWDT2L0_NEWDAT23 _newdt2l0.bit._NEWDAT23
#define NEWDT2L0_NEWDAT24 _newdt2l0.bit._NEWDAT24
__IO_EXTENDED NEWDT2H0STR _newdt2h0;  
#define NEWDT2H0 _newdt2h0.byte
#define NEWDT2H0_NEWDAT25 _newdt2h0.bit._NEWDAT25
#define NEWDT2H0_NEWDAT26 _newdt2h0.bit._NEWDAT26
#define NEWDT2H0_NEWDAT27 _newdt2h0.bit._NEWDAT27
#define NEWDT2H0_NEWDAT28 _newdt2h0.bit._NEWDAT28
#define NEWDT2H0_NEWDAT29 _newdt2h0.bit._NEWDAT29
#define NEWDT2H0_NEWDAT30 _newdt2h0.bit._NEWDAT30
#define NEWDT2H0_NEWDAT31 _newdt2h0.bit._NEWDAT31
#define NEWDT2H0_NEWDAT32 _newdt2h0.bit._NEWDAT32
__IO_EXTENDED INTPND0STR _intpnd0;  
#define INTPND0 _intpnd0.lword
#define INTPND0_INTPND1 _intpnd0.bit._INTPND1
#define INTPND0_INTPND2 _intpnd0.bit._INTPND2
#define INTPND0_INTPND3 _intpnd0.bit._INTPND3
#define INTPND0_INTPND4 _intpnd0.bit._INTPND4
#define INTPND0_INTPND5 _intpnd0.bit._INTPND5
#define INTPND0_INTPND6 _intpnd0.bit._INTPND6
#define INTPND0_INTPND7 _intpnd0.bit._INTPND7
#define INTPND0_INTPND8 _intpnd0.bit._INTPND8
#define INTPND0_INTPND9 _intpnd0.bit._INTPND9
#define INTPND0_INTPND10 _intpnd0.bit._INTPND10
#define INTPND0_INTPND11 _intpnd0.bit._INTPND11
#define INTPND0_INTPND12 _intpnd0.bit._INTPND12
#define INTPND0_INTPND13 _intpnd0.bit._INTPND13
#define INTPND0_INTPND14 _intpnd0.bit._INTPND14
#define INTPND0_INTPND15 _intpnd0.bit._INTPND15
#define INTPND0_INTPND16 _intpnd0.bit._INTPND16
#define INTPND0_INTPND17 _intpnd0.bit._INTPND17
#define INTPND0_INTPND18 _intpnd0.bit._INTPND18
#define INTPND0_INTPND19 _intpnd0.bit._INTPND19
#define INTPND0_INTPND20 _intpnd0.bit._INTPND20
#define INTPND0_INTPND21 _intpnd0.bit._INTPND21
#define INTPND0_INTPND22 _intpnd0.bit._INTPND22
#define INTPND0_INTPND23 _intpnd0.bit._INTPND23
#define INTPND0_INTPND24 _intpnd0.bit._INTPND24
#define INTPND0_INTPND25 _intpnd0.bit._INTPND25
#define INTPND0_INTPND26 _intpnd0.bit._INTPND26
#define INTPND0_INTPND27 _intpnd0.bit._INTPND27
#define INTPND0_INTPND28 _intpnd0.bit._INTPND28
#define INTPND0_INTPND29 _intpnd0.bit._INTPND29
#define INTPND0_INTPND30 _intpnd0.bit._INTPND30
#define INTPND0_INTPND31 _intpnd0.bit._INTPND31
#define INTPND0_INTPND32 _intpnd0.bit._INTPND32
#define INTPND0_INTPND _intpnd0.bitc._INTPND
__IO_EXTENDED INTPND10STR _intpnd10;  
#define INTPND10 _intpnd10.word
#define INTPND10_INTPND1 _intpnd10.bit._INTPND1
#define INTPND10_INTPND2 _intpnd10.bit._INTPND2
#define INTPND10_INTPND3 _intpnd10.bit._INTPND3
#define INTPND10_INTPND4 _intpnd10.bit._INTPND4
#define INTPND10_INTPND5 _intpnd10.bit._INTPND5
#define INTPND10_INTPND6 _intpnd10.bit._INTPND6
#define INTPND10_INTPND7 _intpnd10.bit._INTPND7
#define INTPND10_INTPND8 _intpnd10.bit._INTPND8
#define INTPND10_INTPND9 _intpnd10.bit._INTPND9
#define INTPND10_INTPND10 _intpnd10.bit._INTPND10
#define INTPND10_INTPND11 _intpnd10.bit._INTPND11
#define INTPND10_INTPND12 _intpnd10.bit._INTPND12
#define INTPND10_INTPND13 _intpnd10.bit._INTPND13
#define INTPND10_INTPND14 _intpnd10.bit._INTPND14
#define INTPND10_INTPND15 _intpnd10.bit._INTPND15
#define INTPND10_INTPND16 _intpnd10.bit._INTPND16
__IO_EXTENDED INTPND1L0STR _intpnd1l0;  
#define INTPND1L0 _intpnd1l0.byte
#define INTPND1L0_INTPND1 _intpnd1l0.bit._INTPND1
#define INTPND1L0_INTPND2 _intpnd1l0.bit._INTPND2
#define INTPND1L0_INTPND3 _intpnd1l0.bit._INTPND3
#define INTPND1L0_INTPND4 _intpnd1l0.bit._INTPND4
#define INTPND1L0_INTPND5 _intpnd1l0.bit._INTPND5
#define INTPND1L0_INTPND6 _intpnd1l0.bit._INTPND6
#define INTPND1L0_INTPND7 _intpnd1l0.bit._INTPND7
#define INTPND1L0_INTPND8 _intpnd1l0.bit._INTPND8
__IO_EXTENDED INTPND1H0STR _intpnd1h0;  
#define INTPND1H0 _intpnd1h0.byte
#define INTPND1H0_INTPND9 _intpnd1h0.bit._INTPND9
#define INTPND1H0_INTPND10 _intpnd1h0.bit._INTPND10
#define INTPND1H0_INTPND11 _intpnd1h0.bit._INTPND11
#define INTPND1H0_INTPND12 _intpnd1h0.bit._INTPND12
#define INTPND1H0_INTPND13 _intpnd1h0.bit._INTPND13
#define INTPND1H0_INTPND14 _intpnd1h0.bit._INTPND14
#define INTPND1H0_INTPND15 _intpnd1h0.bit._INTPND15
#define INTPND1H0_INTPND16 _intpnd1h0.bit._INTPND16
__IO_EXTENDED INTPND20STR _intpnd20;  
#define INTPND20 _intpnd20.word
#define INTPND20_INTPND17 _intpnd20.bit._INTPND17
#define INTPND20_INTPND18 _intpnd20.bit._INTPND18
#define INTPND20_INTPND19 _intpnd20.bit._INTPND19
#define INTPND20_INTPND20 _intpnd20.bit._INTPND20
#define INTPND20_INTPND21 _intpnd20.bit._INTPND21
#define INTPND20_INTPND22 _intpnd20.bit._INTPND22
#define INTPND20_INTPND23 _intpnd20.bit._INTPND23
#define INTPND20_INTPND24 _intpnd20.bit._INTPND24
#define INTPND20_INTPND25 _intpnd20.bit._INTPND25
#define INTPND20_INTPND26 _intpnd20.bit._INTPND26
#define INTPND20_INTPND27 _intpnd20.bit._INTPND27
#define INTPND20_INTPND28 _intpnd20.bit._INTPND28
#define INTPND20_INTPND29 _intpnd20.bit._INTPND29
#define INTPND20_INTPND30 _intpnd20.bit._INTPND30
#define INTPND20_INTPND31 _intpnd20.bit._INTPND31
#define INTPND20_INTPND32 _intpnd20.bit._INTPND32
__IO_EXTENDED INTPND2L0STR _intpnd2l0;  
#define INTPND2L0 _intpnd2l0.byte
#define INTPND2L0_INTPND17 _intpnd2l0.bit._INTPND17
#define INTPND2L0_INTPND18 _intpnd2l0.bit._INTPND18
#define INTPND2L0_INTPND19 _intpnd2l0.bit._INTPND19
#define INTPND2L0_INTPND20 _intpnd2l0.bit._INTPND20
#define INTPND2L0_INTPND21 _intpnd2l0.bit._INTPND21
#define INTPND2L0_INTPND22 _intpnd2l0.bit._INTPND22
#define INTPND2L0_INTPND23 _intpnd2l0.bit._INTPND23
#define INTPND2L0_INTPND24 _intpnd2l0.bit._INTPND24
__IO_EXTENDED INTPND2H0STR _intpnd2h0;  
#define INTPND2H0 _intpnd2h0.byte
#define INTPND2H0_INTPND25 _intpnd2h0.bit._INTPND25
#define INTPND2H0_INTPND26 _intpnd2h0.bit._INTPND26
#define INTPND2H0_INTPND27 _intpnd2h0.bit._INTPND27
#define INTPND2H0_INTPND28 _intpnd2h0.bit._INTPND28
#define INTPND2H0_INTPND29 _intpnd2h0.bit._INTPND29
#define INTPND2H0_INTPND30 _intpnd2h0.bit._INTPND30
#define INTPND2H0_INTPND31 _intpnd2h0.bit._INTPND31
#define INTPND2H0_INTPND32 _intpnd2h0.bit._INTPND32
__IO_EXTENDED MSGVAL0STR _msgval0;  
#define MSGVAL0 _msgval0.lword
#define MSGVAL0_MSGVAL1 _msgval0.bit._MSGVAL1
#define MSGVAL0_MSGVAL2 _msgval0.bit._MSGVAL2
#define MSGVAL0_MSGVAL3 _msgval0.bit._MSGVAL3
#define MSGVAL0_MSGVAL4 _msgval0.bit._MSGVAL4
#define MSGVAL0_MSGVAL5 _msgval0.bit._MSGVAL5
#define MSGVAL0_MSGVAL6 _msgval0.bit._MSGVAL6
#define MSGVAL0_MSGVAL7 _msgval0.bit._MSGVAL7
#define MSGVAL0_MSGVAL8 _msgval0.bit._MSGVAL8
#define MSGVAL0_MSGVAL9 _msgval0.bit._MSGVAL9
#define MSGVAL0_MSGVAL10 _msgval0.bit._MSGVAL10
#define MSGVAL0_MSGVAL11 _msgval0.bit._MSGVAL11
#define MSGVAL0_MSGVAL12 _msgval0.bit._MSGVAL12
#define MSGVAL0_MSGVAL13 _msgval0.bit._MSGVAL13
#define MSGVAL0_MSGVAL14 _msgval0.bit._MSGVAL14
#define MSGVAL0_MSGVAL15 _msgval0.bit._MSGVAL15
#define MSGVAL0_MSGVAL16 _msgval0.bit._MSGVAL16
#define MSGVAL0_MSGVAL17 _msgval0.bit._MSGVAL17
#define MSGVAL0_MSGVAL18 _msgval0.bit._MSGVAL18
#define MSGVAL0_MSGVAL19 _msgval0.bit._MSGVAL19
#define MSGVAL0_MSGVAL20 _msgval0.bit._MSGVAL20
#define MSGVAL0_MSGVAL21 _msgval0.bit._MSGVAL21
#define MSGVAL0_MSGVAL22 _msgval0.bit._MSGVAL22
#define MSGVAL0_MSGVAL23 _msgval0.bit._MSGVAL23
#define MSGVAL0_MSGVAL24 _msgval0.bit._MSGVAL24
#define MSGVAL0_MSGVAL25 _msgval0.bit._MSGVAL25
#define MSGVAL0_MSGVAL26 _msgval0.bit._MSGVAL26
#define MSGVAL0_MSGVAL27 _msgval0.bit._MSGVAL27
#define MSGVAL0_MSGVAL28 _msgval0.bit._MSGVAL28
#define MSGVAL0_MSGVAL29 _msgval0.bit._MSGVAL29
#define MSGVAL0_MSGVAL30 _msgval0.bit._MSGVAL30
#define MSGVAL0_MSGVAL31 _msgval0.bit._MSGVAL31
#define MSGVAL0_MSGVAL32 _msgval0.bit._MSGVAL32
#define MSGVAL0_MSGVAL _msgval0.bitc._MSGVAL
__IO_EXTENDED MSGVAL10STR _msgval10;  
#define MSGVAL10 _msgval10.word
#define MSGVAL10_MSGVAL1 _msgval10.bit._MSGVAL1
#define MSGVAL10_MSGVAL2 _msgval10.bit._MSGVAL2
#define MSGVAL10_MSGVAL3 _msgval10.bit._MSGVAL3
#define MSGVAL10_MSGVAL4 _msgval10.bit._MSGVAL4
#define MSGVAL10_MSGVAL5 _msgval10.bit._MSGVAL5
#define MSGVAL10_MSGVAL6 _msgval10.bit._MSGVAL6
#define MSGVAL10_MSGVAL7 _msgval10.bit._MSGVAL7
#define MSGVAL10_MSGVAL8 _msgval10.bit._MSGVAL8
#define MSGVAL10_MSGVAL9 _msgval10.bit._MSGVAL9
#define MSGVAL10_MSGVAL10 _msgval10.bit._MSGVAL10
#define MSGVAL10_MSGVAL11 _msgval10.bit._MSGVAL11
#define MSGVAL10_MSGVAL12 _msgval10.bit._MSGVAL12
#define MSGVAL10_MSGVAL13 _msgval10.bit._MSGVAL13
#define MSGVAL10_MSGVAL14 _msgval10.bit._MSGVAL14
#define MSGVAL10_MSGVAL15 _msgval10.bit._MSGVAL15
#define MSGVAL10_MSGVAL16 _msgval10.bit._MSGVAL16
__IO_EXTENDED MSGVAL1L0STR _msgval1l0;  
#define MSGVAL1L0 _msgval1l0.byte
#define MSGVAL1L0_MSGVAL1 _msgval1l0.bit._MSGVAL1
#define MSGVAL1L0_MSGVAL2 _msgval1l0.bit._MSGVAL2
#define MSGVAL1L0_MSGVAL3 _msgval1l0.bit._MSGVAL3
#define MSGVAL1L0_MSGVAL4 _msgval1l0.bit._MSGVAL4
#define MSGVAL1L0_MSGVAL5 _msgval1l0.bit._MSGVAL5
#define MSGVAL1L0_MSGVAL6 _msgval1l0.bit._MSGVAL6
#define MSGVAL1L0_MSGVAL7 _msgval1l0.bit._MSGVAL7
#define MSGVAL1L0_MSGVAL8 _msgval1l0.bit._MSGVAL8
__IO_EXTENDED MSGVAL1H0STR _msgval1h0;  
#define MSGVAL1H0 _msgval1h0.byte
#define MSGVAL1H0_MSGVAL9 _msgval1h0.bit._MSGVAL9
#define MSGVAL1H0_MSGVAL10 _msgval1h0.bit._MSGVAL10
#define MSGVAL1H0_MSGVAL11 _msgval1h0.bit._MSGVAL11
#define MSGVAL1H0_MSGVAL12 _msgval1h0.bit._MSGVAL12
#define MSGVAL1H0_MSGVAL13 _msgval1h0.bit._MSGVAL13
#define MSGVAL1H0_MSGVAL14 _msgval1h0.bit._MSGVAL14
#define MSGVAL1H0_MSGVAL15 _msgval1h0.bit._MSGVAL15
#define MSGVAL1H0_MSGVAL16 _msgval1h0.bit._MSGVAL16
__IO_EXTENDED MSGVAL20STR _msgval20;  
#define MSGVAL20 _msgval20.word
#define MSGVAL20_MSGVAL17 _msgval20.bit._MSGVAL17
#define MSGVAL20_MSGVAL18 _msgval20.bit._MSGVAL18
#define MSGVAL20_MSGVAL19 _msgval20.bit._MSGVAL19
#define MSGVAL20_MSGVAL20 _msgval20.bit._MSGVAL20
#define MSGVAL20_MSGVAL21 _msgval20.bit._MSGVAL21
#define MSGVAL20_MSGVAL22 _msgval20.bit._MSGVAL22
#define MSGVAL20_MSGVAL23 _msgval20.bit._MSGVAL23
#define MSGVAL20_MSGVAL24 _msgval20.bit._MSGVAL24
#define MSGVAL20_MSGVAL25 _msgval20.bit._MSGVAL25
#define MSGVAL20_MSGVAL26 _msgval20.bit._MSGVAL26
#define MSGVAL20_MSGVAL27 _msgval20.bit._MSGVAL27
#define MSGVAL20_MSGVAL28 _msgval20.bit._MSGVAL28
#define MSGVAL20_MSGVAL29 _msgval20.bit._MSGVAL29
#define MSGVAL20_MSGVAL30 _msgval20.bit._MSGVAL30
#define MSGVAL20_MSGVAL31 _msgval20.bit._MSGVAL31
#define MSGVAL20_MSGVAL32 _msgval20.bit._MSGVAL32
__IO_EXTENDED MSGVAL2L0STR _msgval2l0;  
#define MSGVAL2L0 _msgval2l0.byte
#define MSGVAL2L0_MSGVAL17 _msgval2l0.bit._MSGVAL17
#define MSGVAL2L0_MSGVAL18 _msgval2l0.bit._MSGVAL18
#define MSGVAL2L0_MSGVAL19 _msgval2l0.bit._MSGVAL19
#define MSGVAL2L0_MSGVAL20 _msgval2l0.bit._MSGVAL20
#define MSGVAL2L0_MSGVAL21 _msgval2l0.bit._MSGVAL21
#define MSGVAL2L0_MSGVAL22 _msgval2l0.bit._MSGVAL22
#define MSGVAL2L0_MSGVAL23 _msgval2l0.bit._MSGVAL23
#define MSGVAL2L0_MSGVAL24 _msgval2l0.bit._MSGVAL24
__IO_EXTENDED MSGVAL2H0STR _msgval2h0;  
#define MSGVAL2H0 _msgval2h0.byte
#define MSGVAL2H0_MSGVAL25 _msgval2h0.bit._MSGVAL25
#define MSGVAL2H0_MSGVAL26 _msgval2h0.bit._MSGVAL26
#define MSGVAL2H0_MSGVAL27 _msgval2h0.bit._MSGVAL27
#define MSGVAL2H0_MSGVAL28 _msgval2h0.bit._MSGVAL28
#define MSGVAL2H0_MSGVAL29 _msgval2h0.bit._MSGVAL29
#define MSGVAL2H0_MSGVAL30 _msgval2h0.bit._MSGVAL30
#define MSGVAL2H0_MSGVAL31 _msgval2h0.bit._MSGVAL31
#define MSGVAL2H0_MSGVAL32 _msgval2h0.bit._MSGVAL32
__IO_EXTENDED COER0STR _coer0;  
#define COER0 _coer0.byte
#define COER0_OE _coer0.bit._OE
__IO_EXTENDED CTRLR1STR _ctrlr1;  
#define CTRLR1 _ctrlr1.word
#define CTRLR1_INIT _ctrlr1.bit._INIT
#define CTRLR1_IE _ctrlr1.bit._IE
#define CTRLR1_SIE _ctrlr1.bit._SIE
#define CTRLR1_EIE _ctrlr1.bit._EIE
#define CTRLR1_DAR _ctrlr1.bit._DAR
#define CTRLR1_CCE _ctrlr1.bit._CCE
#define CTRLR1_TEST _ctrlr1.bit._TEST
__IO_EXTENDED CTRLRL1STR _ctrlrl1;  
#define CTRLRL1 _ctrlrl1.byte
#define CTRLRL1_INIT _ctrlrl1.bit._INIT
#define CTRLRL1_IE _ctrlrl1.bit._IE
#define CTRLRL1_SIE _ctrlrl1.bit._SIE
#define CTRLRL1_EIE _ctrlrl1.bit._EIE
#define CTRLRL1_DAR _ctrlrl1.bit._DAR
#define CTRLRL1_CCE _ctrlrl1.bit._CCE
#define CTRLRL1_TEST _ctrlrl1.bit._TEST
__IO_EXTENDED CTRLRH1STR _ctrlrh1;  
#define CTRLRH1 _ctrlrh1.byte
__IO_EXTENDED STATR1STR _statr1;  
#define STATR1 _statr1.word
#define STATR1_LEC0 _statr1.bit._LEC0
#define STATR1_LEC1 _statr1.bit._LEC1
#define STATR1_LEC2 _statr1.bit._LEC2
#define STATR1_TXOK _statr1.bit._TXOK
#define STATR1_RXOK _statr1.bit._RXOK
#define STATR1_EPASS _statr1.bit._EPASS
#define STATR1_EWARN _statr1.bit._EWARN
#define STATR1_BOFF _statr1.bit._BOFF
#define STATR1_LEC _statr1.bitc._LEC
__IO_EXTENDED STATRL1STR _statrl1;  
#define STATRL1 _statrl1.byte
#define STATRL1_LEC0 _statrl1.bit._LEC0
#define STATRL1_LEC1 _statrl1.bit._LEC1
#define STATRL1_LEC2 _statrl1.bit._LEC2
#define STATRL1_TXOK _statrl1.bit._TXOK
#define STATRL1_RXOK _statrl1.bit._RXOK
#define STATRL1_EPASS _statrl1.bit._EPASS
#define STATRL1_EWARN _statrl1.bit._EWARN
#define STATRL1_BOFF _statrl1.bit._BOFF
#define STATRL1_LEC _statrl1.bitc._LEC
__IO_EXTENDED STATRH1STR _statrh1;  
#define STATRH1 _statrh1.byte
__IO_EXTENDED ERRCNT1STR _errcnt1;  
#define ERRCNT1 _errcnt1.word
#define ERRCNT1_TEC0 _errcnt1.bit._TEC0
#define ERRCNT1_TEC1 _errcnt1.bit._TEC1
#define ERRCNT1_TEC2 _errcnt1.bit._TEC2
#define ERRCNT1_TEC3 _errcnt1.bit._TEC3
#define ERRCNT1_TEC4 _errcnt1.bit._TEC4
#define ERRCNT1_TEC5 _errcnt1.bit._TEC5
#define ERRCNT1_TEC6 _errcnt1.bit._TEC6
#define ERRCNT1_TEC7 _errcnt1.bit._TEC7
#define ERRCNT1_REC0 _errcnt1.bit._REC0
#define ERRCNT1_REC1 _errcnt1.bit._REC1
#define ERRCNT1_REC2 _errcnt1.bit._REC2
#define ERRCNT1_REC3 _errcnt1.bit._REC3
#define ERRCNT1_REC4 _errcnt1.bit._REC4
#define ERRCNT1_REC5 _errcnt1.bit._REC5
#define ERRCNT1_REC6 _errcnt1.bit._REC6
#define ERRCNT1_RP _errcnt1.bit._RP
#define ERRCNT1_TEC _errcnt1.bitc._TEC
#define ERRCNT1_REC _errcnt1.bitc._REC
__IO_EXTENDED ERRCNTL1STR _errcntl1;  
#define ERRCNTL1 _errcntl1.byte
#define ERRCNTL1_TEC0 _errcntl1.bit._TEC0
#define ERRCNTL1_TEC1 _errcntl1.bit._TEC1
#define ERRCNTL1_TEC2 _errcntl1.bit._TEC2
#define ERRCNTL1_TEC3 _errcntl1.bit._TEC3
#define ERRCNTL1_TEC4 _errcntl1.bit._TEC4
#define ERRCNTL1_TEC5 _errcntl1.bit._TEC5
#define ERRCNTL1_TEC6 _errcntl1.bit._TEC6
#define ERRCNTL1_TEC7 _errcntl1.bit._TEC7
#define ERRCNTL1_TEC _errcntl1.bitc._TEC
__IO_EXTENDED ERRCNTH1STR _errcnth1;  
#define ERRCNTH1 _errcnth1.byte
#define ERRCNTH1_REC0 _errcnth1.bit._REC0
#define ERRCNTH1_REC1 _errcnth1.bit._REC1
#define ERRCNTH1_REC2 _errcnth1.bit._REC2
#define ERRCNTH1_REC3 _errcnth1.bit._REC3
#define ERRCNTH1_REC4 _errcnth1.bit._REC4
#define ERRCNTH1_REC5 _errcnth1.bit._REC5
#define ERRCNTH1_REC6 _errcnth1.bit._REC6
#define ERRCNTH1_RP _errcnth1.bit._RP
#define ERRCNTH1_REC _errcnth1.bitc._REC
__IO_EXTENDED BTR1STR _btr1;  
#define BTR1 _btr1.word
#define BTR1_BRP0 _btr1.bit._BRP0
#define BTR1_BRP1 _btr1.bit._BRP1
#define BTR1_BRP2 _btr1.bit._BRP2
#define BTR1_BRP3 _btr1.bit._BRP3
#define BTR1_BRP4 _btr1.bit._BRP4
#define BTR1_BRP5 _btr1.bit._BRP5
#define BTR1_SJW0 _btr1.bit._SJW0
#define BTR1_SJW1 _btr1.bit._SJW1
#define BTR1_TSEG10 _btr1.bit._TSEG10
#define BTR1_TSEG11 _btr1.bit._TSEG11
#define BTR1_TSEG12 _btr1.bit._TSEG12
#define BTR1_TSEG13 _btr1.bit._TSEG13
#define BTR1_TSEG20 _btr1.bit._TSEG20
#define BTR1_TSEG21 _btr1.bit._TSEG21
#define BTR1_TSEG22 _btr1.bit._TSEG22
#define BTR1_BRP _btr1.bitc._BRP
#define BTR1_SJW _btr1.bitc._SJW
#define BTR1_TSEG1 _btr1.bitc._TSEG1
#define BTR1_TSEG2 _btr1.bitc._TSEG2
__IO_EXTENDED BTRL1STR _btrl1;  
#define BTRL1 _btrl1.byte
#define BTRL1_BRP0 _btrl1.bit._BRP0
#define BTRL1_BRP1 _btrl1.bit._BRP1
#define BTRL1_BRP2 _btrl1.bit._BRP2
#define BTRL1_BRP3 _btrl1.bit._BRP3
#define BTRL1_BRP4 _btrl1.bit._BRP4
#define BTRL1_BRP5 _btrl1.bit._BRP5
#define BTRL1_SJW0 _btrl1.bit._SJW0
#define BTRL1_SJW1 _btrl1.bit._SJW1
#define BTRL1_BRP _btrl1.bitc._BRP
#define BTRL1_SJW _btrl1.bitc._SJW
__IO_EXTENDED BTRH1STR _btrh1;  
#define BTRH1 _btrh1.byte
#define BTRH1_TSEG10 _btrh1.bit._TSEG10
#define BTRH1_TSEG11 _btrh1.bit._TSEG11
#define BTRH1_TSEG12 _btrh1.bit._TSEG12
#define BTRH1_TSEG13 _btrh1.bit._TSEG13
#define BTRH1_TSEG20 _btrh1.bit._TSEG20
#define BTRH1_TSEG21 _btrh1.bit._TSEG21
#define BTRH1_TSEG22 _btrh1.bit._TSEG22
#define BTRH1_TSEG1 _btrh1.bitc._TSEG1
#define BTRH1_TSEG2 _btrh1.bitc._TSEG2
__IO_EXTENDED INTR1STR _intr1;  
#define INTR1 _intr1.word
#define INTR1_INTID0 _intr1.bit._INTID0
#define INTR1_INTID1 _intr1.bit._INTID1
#define INTR1_INTID2 _intr1.bit._INTID2
#define INTR1_INTID3 _intr1.bit._INTID3
#define INTR1_INTID4 _intr1.bit._INTID4
#define INTR1_INTID5 _intr1.bit._INTID5
#define INTR1_INTID6 _intr1.bit._INTID6
#define INTR1_INTID7 _intr1.bit._INTID7
#define INTR1_INTID8 _intr1.bit._INTID8
#define INTR1_INTID9 _intr1.bit._INTID9
#define INTR1_INTID10 _intr1.bit._INTID10
#define INTR1_INTID11 _intr1.bit._INTID11
#define INTR1_INTID12 _intr1.bit._INTID12
#define INTR1_INTID13 _intr1.bit._INTID13
#define INTR1_INTID14 _intr1.bit._INTID14
#define INTR1_INTID15 _intr1.bit._INTID15
#define INTR1_INTID _intr1.bitc._INTID
__IO_EXTENDED INTRL1STR _intrl1;  
#define INTRL1 _intrl1.byte
#define INTRL1_INTID0 _intrl1.bit._INTID0
#define INTRL1_INTID1 _intrl1.bit._INTID1
#define INTRL1_INTID2 _intrl1.bit._INTID2
#define INTRL1_INTID3 _intrl1.bit._INTID3
#define INTRL1_INTID4 _intrl1.bit._INTID4
#define INTRL1_INTID5 _intrl1.bit._INTID5
#define INTRL1_INTID6 _intrl1.bit._INTID6
#define INTRL1_INTID7 _intrl1.bit._INTID7
__IO_EXTENDED INTRH1STR _intrh1;  
#define INTRH1 _intrh1.byte
#define INTRH1_INTID8 _intrh1.bit._INTID8
#define INTRH1_INTID9 _intrh1.bit._INTID9
#define INTRH1_INTID10 _intrh1.bit._INTID10
#define INTRH1_INTID11 _intrh1.bit._INTID11
#define INTRH1_INTID12 _intrh1.bit._INTID12
#define INTRH1_INTID13 _intrh1.bit._INTID13
#define INTRH1_INTID14 _intrh1.bit._INTID14
#define INTRH1_INTID15 _intrh1.bit._INTID15
__IO_EXTENDED TESTR1STR _testr1;  
#define TESTR1 _testr1.word
#define TESTR1_BASIC _testr1.bit._BASIC
#define TESTR1_SILENT _testr1.bit._SILENT
#define TESTR1_LBACK _testr1.bit._LBACK
#define TESTR1_TX0 _testr1.bit._TX0
#define TESTR1_TX1 _testr1.bit._TX1
#define TESTR1_RX _testr1.bit._RX
__IO_EXTENDED TESTRL1STR _testrl1;  
#define TESTRL1 _testrl1.byte
#define TESTRL1_BASIC _testrl1.bit._BASIC
#define TESTRL1_SILENT _testrl1.bit._SILENT
#define TESTRL1_LBACK _testrl1.bit._LBACK
#define TESTRL1_TX0 _testrl1.bit._TX0
#define TESTRL1_TX1 _testrl1.bit._TX1
#define TESTRL1_RX _testrl1.bit._RX
__IO_EXTENDED TESTRH1STR _testrh1;  
#define TESTRH1 _testrh1.byte
__IO_EXTENDED BRPER1STR _brper1;  
#define BRPER1 _brper1.word
#define BRPER1_BRPE0 _brper1.bit._BRPE0
#define BRPER1_BRPE1 _brper1.bit._BRPE1
#define BRPER1_BRPE2 _brper1.bit._BRPE2
#define BRPER1_BRPE3 _brper1.bit._BRPE3
#define BRPER1_BRPE _brper1.bitc._BRPE
__IO_EXTENDED BRPERL1STR _brperl1;  
#define BRPERL1 _brperl1.byte
#define BRPERL1_BRPE0 _brperl1.bit._BRPE0
#define BRPERL1_BRPE1 _brperl1.bit._BRPE1
#define BRPERL1_BRPE2 _brperl1.bit._BRPE2
#define BRPERL1_BRPE3 _brperl1.bit._BRPE3
#define BRPERL1_BRPE _brperl1.bitc._BRPE
__IO_EXTENDED BRPERH1STR _brperh1;  
#define BRPERH1 _brperh1.byte
__IO_EXTENDED IF1CREQ1STR _if1creq1;  
#define IF1CREQ1 _if1creq1.word
#define IF1CREQ1_MSGN0 _if1creq1.bit._MSGN0
#define IF1CREQ1_MSGN1 _if1creq1.bit._MSGN1
#define IF1CREQ1_MSGN2 _if1creq1.bit._MSGN2
#define IF1CREQ1_MSGN3 _if1creq1.bit._MSGN3
#define IF1CREQ1_MSGN4 _if1creq1.bit._MSGN4
#define IF1CREQ1_MSGN5 _if1creq1.bit._MSGN5
#define IF1CREQ1_MSGN6 _if1creq1.bit._MSGN6
#define IF1CREQ1_MSGN7 _if1creq1.bit._MSGN7
#define IF1CREQ1_BUSY _if1creq1.bit._BUSY
__IO_EXTENDED IF1CREQL1STR _if1creql1;  
#define IF1CREQL1 _if1creql1.byte
#define IF1CREQL1_MSGN0 _if1creql1.bit._MSGN0
#define IF1CREQL1_MSGN1 _if1creql1.bit._MSGN1
#define IF1CREQL1_MSGN2 _if1creql1.bit._MSGN2
#define IF1CREQL1_MSGN3 _if1creql1.bit._MSGN3
#define IF1CREQL1_MSGN4 _if1creql1.bit._MSGN4
#define IF1CREQL1_MSGN5 _if1creql1.bit._MSGN5
#define IF1CREQL1_MSGN6 _if1creql1.bit._MSGN6
#define IF1CREQL1_MSGN7 _if1creql1.bit._MSGN7
__IO_EXTENDED IF1CREQH1STR _if1creqh1;  
#define IF1CREQH1 _if1creqh1.byte
#define IF1CREQH1_BUSY _if1creqh1.bit._BUSY
__IO_EXTENDED IF1CMSK1STR _if1cmsk1;  
#define IF1CMSK1 _if1cmsk1.word
#define IF1CMSK1_DATAB _if1cmsk1.bit._DATAB
#define IF1CMSK1_DATAA _if1cmsk1.bit._DATAA
#define IF1CMSK1_TXREQ _if1cmsk1.bit._TXREQ
#define IF1CMSK1_CIP _if1cmsk1.bit._CIP
#define IF1CMSK1_CONTROL _if1cmsk1.bit._CONTROL
#define IF1CMSK1_ARB _if1cmsk1.bit._ARB
#define IF1CMSK1_MASK _if1cmsk1.bit._MASK
#define IF1CMSK1_WRRD _if1cmsk1.bit._WRRD
__IO_EXTENDED IF1CMSKL1STR _if1cmskl1;  
#define IF1CMSKL1 _if1cmskl1.byte
#define IF1CMSKL1_DATAB _if1cmskl1.bit._DATAB
#define IF1CMSKL1_DATAA _if1cmskl1.bit._DATAA
#define IF1CMSKL1_TXREQ _if1cmskl1.bit._TXREQ
#define IF1CMSKL1_CIP _if1cmskl1.bit._CIP
#define IF1CMSKL1_CONTROL _if1cmskl1.bit._CONTROL
#define IF1CMSKL1_ARB _if1cmskl1.bit._ARB
#define IF1CMSKL1_MASK _if1cmskl1.bit._MASK
#define IF1CMSKL1_WRRD _if1cmskl1.bit._WRRD
__IO_EXTENDED IF1CMSKH1STR _if1cmskh1;  
#define IF1CMSKH1 _if1cmskh1.byte
__IO_EXTENDED IF1MSK1STR _if1msk1;  
#define IF1MSK1 _if1msk1.lword
#define IF1MSK1_MSK0 _if1msk1.bit._MSK0
#define IF1MSK1_MSK1 _if1msk1.bit._MSK1
#define IF1MSK1_MSK2 _if1msk1.bit._MSK2
#define IF1MSK1_MSK3 _if1msk1.bit._MSK3
#define IF1MSK1_MSK4 _if1msk1.bit._MSK4
#define IF1MSK1_MSK5 _if1msk1.bit._MSK5
#define IF1MSK1_MSK6 _if1msk1.bit._MSK6
#define IF1MSK1_MSK7 _if1msk1.bit._MSK7
#define IF1MSK1_MSK8 _if1msk1.bit._MSK8
#define IF1MSK1_MSK9 _if1msk1.bit._MSK9
#define IF1MSK1_MSK10 _if1msk1.bit._MSK10
#define IF1MSK1_MSK11 _if1msk1.bit._MSK11
#define IF1MSK1_MSK12 _if1msk1.bit._MSK12
#define IF1MSK1_MSK13 _if1msk1.bit._MSK13
#define IF1MSK1_MSK14 _if1msk1.bit._MSK14
#define IF1MSK1_MSK15 _if1msk1.bit._MSK15
#define IF1MSK1_MSK16 _if1msk1.bit._MSK16
#define IF1MSK1_MSK17 _if1msk1.bit._MSK17
#define IF1MSK1_MSK18 _if1msk1.bit._MSK18
#define IF1MSK1_MSK19 _if1msk1.bit._MSK19
#define IF1MSK1_MSK20 _if1msk1.bit._MSK20
#define IF1MSK1_MSK21 _if1msk1.bit._MSK21
#define IF1MSK1_MSK22 _if1msk1.bit._MSK22
#define IF1MSK1_MSK23 _if1msk1.bit._MSK23
#define IF1MSK1_MSK24 _if1msk1.bit._MSK24
#define IF1MSK1_MSK25 _if1msk1.bit._MSK25
#define IF1MSK1_MSK26 _if1msk1.bit._MSK26
#define IF1MSK1_MSK27 _if1msk1.bit._MSK27
#define IF1MSK1_MSK28 _if1msk1.bit._MSK28
#define IF1MSK1_MDIR _if1msk1.bit._MDIR
#define IF1MSK1_MXTD _if1msk1.bit._MXTD
#define IF1MSK1_MSK _if1msk1.bitc._MSK
__IO_EXTENDED IF1MSK11STR _if1msk11;  
#define IF1MSK11 _if1msk11.word
#define IF1MSK11_MSK0 _if1msk11.bit._MSK0
#define IF1MSK11_MSK1 _if1msk11.bit._MSK1
#define IF1MSK11_MSK2 _if1msk11.bit._MSK2
#define IF1MSK11_MSK3 _if1msk11.bit._MSK3
#define IF1MSK11_MSK4 _if1msk11.bit._MSK4
#define IF1MSK11_MSK5 _if1msk11.bit._MSK5
#define IF1MSK11_MSK6 _if1msk11.bit._MSK6
#define IF1MSK11_MSK7 _if1msk11.bit._MSK7
#define IF1MSK11_MSK8 _if1msk11.bit._MSK8
#define IF1MSK11_MSK9 _if1msk11.bit._MSK9
#define IF1MSK11_MSK10 _if1msk11.bit._MSK10
#define IF1MSK11_MSK11 _if1msk11.bit._MSK11
#define IF1MSK11_MSK12 _if1msk11.bit._MSK12
#define IF1MSK11_MSK13 _if1msk11.bit._MSK13
#define IF1MSK11_MSK14 _if1msk11.bit._MSK14
#define IF1MSK11_MSK15 _if1msk11.bit._MSK15
__IO_EXTENDED IF1MSK1L1STR _if1msk1l1;  
#define IF1MSK1L1 _if1msk1l1.byte
#define IF1MSK1L1_MSK0 _if1msk1l1.bit._MSK0
#define IF1MSK1L1_MSK1 _if1msk1l1.bit._MSK1
#define IF1MSK1L1_MSK2 _if1msk1l1.bit._MSK2
#define IF1MSK1L1_MSK3 _if1msk1l1.bit._MSK3
#define IF1MSK1L1_MSK4 _if1msk1l1.bit._MSK4
#define IF1MSK1L1_MSK5 _if1msk1l1.bit._MSK5
#define IF1MSK1L1_MSK6 _if1msk1l1.bit._MSK6
#define IF1MSK1L1_MSK7 _if1msk1l1.bit._MSK7
__IO_EXTENDED IF1MSK1H1STR _if1msk1h1;  
#define IF1MSK1H1 _if1msk1h1.byte
#define IF1MSK1H1_MSK8 _if1msk1h1.bit._MSK8
#define IF1MSK1H1_MSK9 _if1msk1h1.bit._MSK9
#define IF1MSK1H1_MSK10 _if1msk1h1.bit._MSK10
#define IF1MSK1H1_MSK11 _if1msk1h1.bit._MSK11
#define IF1MSK1H1_MSK12 _if1msk1h1.bit._MSK12
#define IF1MSK1H1_MSK13 _if1msk1h1.bit._MSK13
#define IF1MSK1H1_MSK14 _if1msk1h1.bit._MSK14
#define IF1MSK1H1_MSK15 _if1msk1h1.bit._MSK15
__IO_EXTENDED IF1MSK21STR _if1msk21;  
#define IF1MSK21 _if1msk21.word
#define IF1MSK21_MSK16 _if1msk21.bit._MSK16
#define IF1MSK21_MSK17 _if1msk21.bit._MSK17
#define IF1MSK21_MSK18 _if1msk21.bit._MSK18
#define IF1MSK21_MSK19 _if1msk21.bit._MSK19
#define IF1MSK21_MSK20 _if1msk21.bit._MSK20
#define IF1MSK21_MSK21 _if1msk21.bit._MSK21
#define IF1MSK21_MSK22 _if1msk21.bit._MSK22
#define IF1MSK21_MSK23 _if1msk21.bit._MSK23
#define IF1MSK21_MSK24 _if1msk21.bit._MSK24
#define IF1MSK21_MSK25 _if1msk21.bit._MSK25
#define IF1MSK21_MSK26 _if1msk21.bit._MSK26
#define IF1MSK21_MSK27 _if1msk21.bit._MSK27
#define IF1MSK21_MSK28 _if1msk21.bit._MSK28
#define IF1MSK21_MDIR _if1msk21.bit._MDIR
#define IF1MSK21_MXTD _if1msk21.bit._MXTD
__IO_EXTENDED IF1MSK2L1STR _if1msk2l1;  
#define IF1MSK2L1 _if1msk2l1.byte
#define IF1MSK2L1_MSK16 _if1msk2l1.bit._MSK16
#define IF1MSK2L1_MSK17 _if1msk2l1.bit._MSK17
#define IF1MSK2L1_MSK18 _if1msk2l1.bit._MSK18
#define IF1MSK2L1_MSK19 _if1msk2l1.bit._MSK19
#define IF1MSK2L1_MSK20 _if1msk2l1.bit._MSK20
#define IF1MSK2L1_MSK21 _if1msk2l1.bit._MSK21
#define IF1MSK2L1_MSK22 _if1msk2l1.bit._MSK22
#define IF1MSK2L1_MSK23 _if1msk2l1.bit._MSK23
__IO_EXTENDED IF1MSK2H1STR _if1msk2h1;  
#define IF1MSK2H1 _if1msk2h1.byte
#define IF1MSK2H1_MSK24 _if1msk2h1.bit._MSK24
#define IF1MSK2H1_MSK25 _if1msk2h1.bit._MSK25
#define IF1MSK2H1_MSK26 _if1msk2h1.bit._MSK26
#define IF1MSK2H1_MSK27 _if1msk2h1.bit._MSK27
#define IF1MSK2H1_MSK28 _if1msk2h1.bit._MSK28
#define IF1MSK2H1_MDIR _if1msk2h1.bit._MDIR
#define IF1MSK2H1_MXTD _if1msk2h1.bit._MXTD
__IO_EXTENDED IF1ARB1STR _if1arb1;  
#define IF1ARB1 _if1arb1.lword
#define IF1ARB1_ID0 _if1arb1.bit._ID0
#define IF1ARB1_ID1 _if1arb1.bit._ID1
#define IF1ARB1_ID2 _if1arb1.bit._ID2
#define IF1ARB1_ID3 _if1arb1.bit._ID3
#define IF1ARB1_ID4 _if1arb1.bit._ID4
#define IF1ARB1_ID5 _if1arb1.bit._ID5
#define IF1ARB1_ID6 _if1arb1.bit._ID6
#define IF1ARB1_ID7 _if1arb1.bit._ID7
#define IF1ARB1_ID8 _if1arb1.bit._ID8
#define IF1ARB1_ID9 _if1arb1.bit._ID9
#define IF1ARB1_ID10 _if1arb1.bit._ID10
#define IF1ARB1_ID11 _if1arb1.bit._ID11
#define IF1ARB1_ID12 _if1arb1.bit._ID12
#define IF1ARB1_ID13 _if1arb1.bit._ID13
#define IF1ARB1_ID14 _if1arb1.bit._ID14
#define IF1ARB1_ID15 _if1arb1.bit._ID15
#define IF1ARB1_ID16 _if1arb1.bit._ID16
#define IF1ARB1_ID17 _if1arb1.bit._ID17
#define IF1ARB1_ID18 _if1arb1.bit._ID18
#define IF1ARB1_ID19 _if1arb1.bit._ID19
#define IF1ARB1_ID20 _if1arb1.bit._ID20
#define IF1ARB1_ID21 _if1arb1.bit._ID21
#define IF1ARB1_ID22 _if1arb1.bit._ID22
#define IF1ARB1_ID23 _if1arb1.bit._ID23
#define IF1ARB1_ID24 _if1arb1.bit._ID24
#define IF1ARB1_ID25 _if1arb1.bit._ID25
#define IF1ARB1_ID26 _if1arb1.bit._ID26
#define IF1ARB1_ID27 _if1arb1.bit._ID27
#define IF1ARB1_ID28 _if1arb1.bit._ID28
#define IF1ARB1_DIR _if1arb1.bit._DIR
#define IF1ARB1_XTD _if1arb1.bit._XTD
#define IF1ARB1_MSGVAL _if1arb1.bit._MSGVAL
#define IF1ARB1_ID _if1arb1.bitc._ID
__IO_EXTENDED IF1ARB11STR _if1arb11;  
#define IF1ARB11 _if1arb11.word
#define IF1ARB11_ID0 _if1arb11.bit._ID0
#define IF1ARB11_ID1 _if1arb11.bit._ID1
#define IF1ARB11_ID2 _if1arb11.bit._ID2
#define IF1ARB11_ID3 _if1arb11.bit._ID3
#define IF1ARB11_ID4 _if1arb11.bit._ID4
#define IF1ARB11_ID5 _if1arb11.bit._ID5
#define IF1ARB11_ID6 _if1arb11.bit._ID6
#define IF1ARB11_ID7 _if1arb11.bit._ID7
#define IF1ARB11_ID8 _if1arb11.bit._ID8
#define IF1ARB11_ID9 _if1arb11.bit._ID9
#define IF1ARB11_ID10 _if1arb11.bit._ID10
#define IF1ARB11_ID11 _if1arb11.bit._ID11
#define IF1ARB11_ID12 _if1arb11.bit._ID12
#define IF1ARB11_ID13 _if1arb11.bit._ID13
#define IF1ARB11_ID14 _if1arb11.bit._ID14
#define IF1ARB11_ID15 _if1arb11.bit._ID15
__IO_EXTENDED IF1ARB1L1STR _if1arb1l1;  
#define IF1ARB1L1 _if1arb1l1.byte
#define IF1ARB1L1_ID0 _if1arb1l1.bit._ID0
#define IF1ARB1L1_ID1 _if1arb1l1.bit._ID1
#define IF1ARB1L1_ID2 _if1arb1l1.bit._ID2
#define IF1ARB1L1_ID3 _if1arb1l1.bit._ID3
#define IF1ARB1L1_ID4 _if1arb1l1.bit._ID4
#define IF1ARB1L1_ID5 _if1arb1l1.bit._ID5
#define IF1ARB1L1_ID6 _if1arb1l1.bit._ID6
#define IF1ARB1L1_ID7 _if1arb1l1.bit._ID7
__IO_EXTENDED IF1ARB1H1STR _if1arb1h1;  
#define IF1ARB1H1 _if1arb1h1.byte
#define IF1ARB1H1_ID8 _if1arb1h1.bit._ID8
#define IF1ARB1H1_ID9 _if1arb1h1.bit._ID9
#define IF1ARB1H1_ID10 _if1arb1h1.bit._ID10
#define IF1ARB1H1_ID11 _if1arb1h1.bit._ID11
#define IF1ARB1H1_ID12 _if1arb1h1.bit._ID12
#define IF1ARB1H1_ID13 _if1arb1h1.bit._ID13
#define IF1ARB1H1_ID14 _if1arb1h1.bit._ID14
#define IF1ARB1H1_ID15 _if1arb1h1.bit._ID15
__IO_EXTENDED IF1ARB21STR _if1arb21;  
#define IF1ARB21 _if1arb21.word
#define IF1ARB21_ID16 _if1arb21.bit._ID16
#define IF1ARB21_ID17 _if1arb21.bit._ID17
#define IF1ARB21_ID18 _if1arb21.bit._ID18
#define IF1ARB21_ID19 _if1arb21.bit._ID19
#define IF1ARB21_ID20 _if1arb21.bit._ID20
#define IF1ARB21_ID21 _if1arb21.bit._ID21
#define IF1ARB21_ID22 _if1arb21.bit._ID22
#define IF1ARB21_ID23 _if1arb21.bit._ID23
#define IF1ARB21_ID24 _if1arb21.bit._ID24
#define IF1ARB21_ID25 _if1arb21.bit._ID25
#define IF1ARB21_ID26 _if1arb21.bit._ID26
#define IF1ARB21_ID27 _if1arb21.bit._ID27
#define IF1ARB21_ID28 _if1arb21.bit._ID28
#define IF1ARB21_DIR _if1arb21.bit._DIR
#define IF1ARB21_XTD _if1arb21.bit._XTD
#define IF1ARB21_MSGVAL _if1arb21.bit._MSGVAL
__IO_EXTENDED IF1ARB2L1STR _if1arb2l1;  
#define IF1ARB2L1 _if1arb2l1.byte
#define IF1ARB2L1_ID16 _if1arb2l1.bit._ID16
#define IF1ARB2L1_ID17 _if1arb2l1.bit._ID17
#define IF1ARB2L1_ID18 _if1arb2l1.bit._ID18
#define IF1ARB2L1_ID19 _if1arb2l1.bit._ID19
#define IF1ARB2L1_ID20 _if1arb2l1.bit._ID20
#define IF1ARB2L1_ID21 _if1arb2l1.bit._ID21
#define IF1ARB2L1_ID22 _if1arb2l1.bit._ID22
#define IF1ARB2L1_ID23 _if1arb2l1.bit._ID23
__IO_EXTENDED IF1ARB2H1STR _if1arb2h1;  
#define IF1ARB2H1 _if1arb2h1.byte
#define IF1ARB2H1_ID24 _if1arb2h1.bit._ID24
#define IF1ARB2H1_ID25 _if1arb2h1.bit._ID25
#define IF1ARB2H1_ID26 _if1arb2h1.bit._ID26
#define IF1ARB2H1_ID27 _if1arb2h1.bit._ID27
#define IF1ARB2H1_ID28 _if1arb2h1.bit._ID28
#define IF1ARB2H1_DIR _if1arb2h1.bit._DIR
#define IF1ARB2H1_XTD _if1arb2h1.bit._XTD
#define IF1ARB2H1_MSGVAL _if1arb2h1.bit._MSGVAL
__IO_EXTENDED IF1MCTR1STR _if1mctr1;  
#define IF1MCTR1 _if1mctr1.word
#define IF1MCTR1_DLC0 _if1mctr1.bit._DLC0
#define IF1MCTR1_DLC1 _if1mctr1.bit._DLC1
#define IF1MCTR1_DLC2 _if1mctr1.bit._DLC2
#define IF1MCTR1_DLC3 _if1mctr1.bit._DLC3
#define IF1MCTR1_EOB _if1mctr1.bit._EOB
#define IF1MCTR1_TXRQST _if1mctr1.bit._TXRQST
#define IF1MCTR1_RMTEN _if1mctr1.bit._RMTEN
#define IF1MCTR1_RXIE _if1mctr1.bit._RXIE
#define IF1MCTR1_TXIE _if1mctr1.bit._TXIE
#define IF1MCTR1_UMASK _if1mctr1.bit._UMASK
#define IF1MCTR1_INTPND _if1mctr1.bit._INTPND
#define IF1MCTR1_MSGLST _if1mctr1.bit._MSGLST
#define IF1MCTR1_NEWDAT _if1mctr1.bit._NEWDAT
#define IF1MCTR1_DLC _if1mctr1.bitc._DLC
__IO_EXTENDED IF1MCTRL1STR _if1mctrl1;  
#define IF1MCTRL1 _if1mctrl1.byte
#define IF1MCTRL1_DLC0 _if1mctrl1.bit._DLC0
#define IF1MCTRL1_DLC1 _if1mctrl1.bit._DLC1
#define IF1MCTRL1_DLC2 _if1mctrl1.bit._DLC2
#define IF1MCTRL1_DLC3 _if1mctrl1.bit._DLC3
#define IF1MCTRL1_EOB _if1mctrl1.bit._EOB
#define IF1MCTRL1_DLC _if1mctrl1.bitc._DLC
__IO_EXTENDED IF1MCTRH1STR _if1mctrh1;  
#define IF1MCTRH1 _if1mctrh1.byte
#define IF1MCTRH1_TXRQST _if1mctrh1.bit._TXRQST
#define IF1MCTRH1_RMTEN _if1mctrh1.bit._RMTEN
#define IF1MCTRH1_RXIE _if1mctrh1.bit._RXIE
#define IF1MCTRH1_TXIE _if1mctrh1.bit._TXIE
#define IF1MCTRH1_UMASK _if1mctrh1.bit._UMASK
#define IF1MCTRH1_INTPND _if1mctrh1.bit._INTPND
#define IF1MCTRH1_MSGLST _if1mctrh1.bit._MSGLST
#define IF1MCTRH1_NEWDAT _if1mctrh1.bit._NEWDAT
__IO_EXTENDED IF1DTA1STR _if1dta1;  
#define IF1DTA1 _if1dta1.lword
__IO_EXTENDED IF1DTA11STR _if1dta11;  
#define IF1DTA11 _if1dta11.word
__IO_EXTENDED IF1DTA1L1STR _if1dta1l1;  
#define IF1DTA1L1 _if1dta1l1.byte
__IO_EXTENDED IF1DTA1H1STR _if1dta1h1;  
#define IF1DTA1H1 _if1dta1h1.byte
__IO_EXTENDED IF1DTA21STR _if1dta21;  
#define IF1DTA21 _if1dta21.word
__IO_EXTENDED IF1DTA2L1STR _if1dta2l1;  
#define IF1DTA2L1 _if1dta2l1.byte
__IO_EXTENDED IF1DTA2H1STR _if1dta2h1;  
#define IF1DTA2H1 _if1dta2h1.byte
__IO_EXTENDED IF1DTB1STR _if1dtb1;  
#define IF1DTB1 _if1dtb1.lword
__IO_EXTENDED IF1DTB11STR _if1dtb11;  
#define IF1DTB11 _if1dtb11.word
__IO_EXTENDED IF1DTB1L1STR _if1dtb1l1;  
#define IF1DTB1L1 _if1dtb1l1.byte
__IO_EXTENDED IF1DTB1H1STR _if1dtb1h1;  
#define IF1DTB1H1 _if1dtb1h1.byte
__IO_EXTENDED IF1DTB21STR _if1dtb21;  
#define IF1DTB21 _if1dtb21.word
__IO_EXTENDED IF1DTB2L1STR _if1dtb2l1;  
#define IF1DTB2L1 _if1dtb2l1.byte
__IO_EXTENDED IF1DTB2H1STR _if1dtb2h1;  
#define IF1DTB2H1 _if1dtb2h1.byte
__IO_EXTENDED IF2CREQ1STR _if2creq1;  
#define IF2CREQ1 _if2creq1.word
#define IF2CREQ1_MSGN0 _if2creq1.bit._MSGN0
#define IF2CREQ1_MSGN1 _if2creq1.bit._MSGN1
#define IF2CREQ1_MSGN2 _if2creq1.bit._MSGN2
#define IF2CREQ1_MSGN3 _if2creq1.bit._MSGN3
#define IF2CREQ1_MSGN4 _if2creq1.bit._MSGN4
#define IF2CREQ1_MSGN5 _if2creq1.bit._MSGN5
#define IF2CREQ1_MSGN6 _if2creq1.bit._MSGN6
#define IF2CREQ1_MSGN7 _if2creq1.bit._MSGN7
#define IF2CREQ1_BUSY _if2creq1.bit._BUSY
__IO_EXTENDED IF2CREQL1STR _if2creql1;  
#define IF2CREQL1 _if2creql1.byte
#define IF2CREQL1_MSGN0 _if2creql1.bit._MSGN0
#define IF2CREQL1_MSGN1 _if2creql1.bit._MSGN1
#define IF2CREQL1_MSGN2 _if2creql1.bit._MSGN2
#define IF2CREQL1_MSGN3 _if2creql1.bit._MSGN3
#define IF2CREQL1_MSGN4 _if2creql1.bit._MSGN4
#define IF2CREQL1_MSGN5 _if2creql1.bit._MSGN5
#define IF2CREQL1_MSGN6 _if2creql1.bit._MSGN6
#define IF2CREQL1_MSGN7 _if2creql1.bit._MSGN7
__IO_EXTENDED IF2CREQH1STR _if2creqh1;  
#define IF2CREQH1 _if2creqh1.byte
#define IF2CREQH1_BUSY _if2creqh1.bit._BUSY
__IO_EXTENDED IF2CMSK1STR _if2cmsk1;  
#define IF2CMSK1 _if2cmsk1.word
#define IF2CMSK1_DATAB _if2cmsk1.bit._DATAB
#define IF2CMSK1_DATAA _if2cmsk1.bit._DATAA
#define IF2CMSK1_TXREQ _if2cmsk1.bit._TXREQ
#define IF2CMSK1_CIP _if2cmsk1.bit._CIP
#define IF2CMSK1_CONTROL _if2cmsk1.bit._CONTROL
#define IF2CMSK1_ARB _if2cmsk1.bit._ARB
#define IF2CMSK1_MASK _if2cmsk1.bit._MASK
#define IF2CMSK1_WRRD _if2cmsk1.bit._WRRD
__IO_EXTENDED IF2CMSKL1STR _if2cmskl1;  
#define IF2CMSKL1 _if2cmskl1.byte
#define IF2CMSKL1_DATAB _if2cmskl1.bit._DATAB
#define IF2CMSKL1_DATAA _if2cmskl1.bit._DATAA
#define IF2CMSKL1_TXREQ _if2cmskl1.bit._TXREQ
#define IF2CMSKL1_CIP _if2cmskl1.bit._CIP
#define IF2CMSKL1_CONTROL _if2cmskl1.bit._CONTROL
#define IF2CMSKL1_ARB _if2cmskl1.bit._ARB
#define IF2CMSKL1_MASK _if2cmskl1.bit._MASK
#define IF2CMSKL1_WRRD _if2cmskl1.bit._WRRD
__IO_EXTENDED IF2CMSKH1STR _if2cmskh1;  
#define IF2CMSKH1 _if2cmskh1.byte
__IO_EXTENDED IF2MSK1STR _if2msk1;  
#define IF2MSK1 _if2msk1.lword
#define IF2MSK1_MSK0 _if2msk1.bit._MSK0
#define IF2MSK1_MSK1 _if2msk1.bit._MSK1
#define IF2MSK1_MSK2 _if2msk1.bit._MSK2
#define IF2MSK1_MSK3 _if2msk1.bit._MSK3
#define IF2MSK1_MSK4 _if2msk1.bit._MSK4
#define IF2MSK1_MSK5 _if2msk1.bit._MSK5
#define IF2MSK1_MSK6 _if2msk1.bit._MSK6
#define IF2MSK1_MSK7 _if2msk1.bit._MSK7
#define IF2MSK1_MSK8 _if2msk1.bit._MSK8
#define IF2MSK1_MSK9 _if2msk1.bit._MSK9
#define IF2MSK1_MSK10 _if2msk1.bit._MSK10
#define IF2MSK1_MSK11 _if2msk1.bit._MSK11
#define IF2MSK1_MSK12 _if2msk1.bit._MSK12
#define IF2MSK1_MSK13 _if2msk1.bit._MSK13
#define IF2MSK1_MSK14 _if2msk1.bit._MSK14
#define IF2MSK1_MSK15 _if2msk1.bit._MSK15
#define IF2MSK1_MSK16 _if2msk1.bit._MSK16
#define IF2MSK1_MSK17 _if2msk1.bit._MSK17
#define IF2MSK1_MSK18 _if2msk1.bit._MSK18
#define IF2MSK1_MSK19 _if2msk1.bit._MSK19
#define IF2MSK1_MSK20 _if2msk1.bit._MSK20
#define IF2MSK1_MSK21 _if2msk1.bit._MSK21
#define IF2MSK1_MSK22 _if2msk1.bit._MSK22
#define IF2MSK1_MSK23 _if2msk1.bit._MSK23
#define IF2MSK1_MSK24 _if2msk1.bit._MSK24
#define IF2MSK1_MSK25 _if2msk1.bit._MSK25
#define IF2MSK1_MSK26 _if2msk1.bit._MSK26
#define IF2MSK1_MSK27 _if2msk1.bit._MSK27
#define IF2MSK1_MSK28 _if2msk1.bit._MSK28
#define IF2MSK1_MDIR _if2msk1.bit._MDIR
#define IF2MSK1_MXTD _if2msk1.bit._MXTD
#define IF2MSK1_MSK _if2msk1.bitc._MSK
__IO_EXTENDED IF2MSK11STR _if2msk11;  
#define IF2MSK11 _if2msk11.word
#define IF2MSK11_MSK0 _if2msk11.bit._MSK0
#define IF2MSK11_MSK1 _if2msk11.bit._MSK1
#define IF2MSK11_MSK2 _if2msk11.bit._MSK2
#define IF2MSK11_MSK3 _if2msk11.bit._MSK3
#define IF2MSK11_MSK4 _if2msk11.bit._MSK4
#define IF2MSK11_MSK5 _if2msk11.bit._MSK5
#define IF2MSK11_MSK6 _if2msk11.bit._MSK6
#define IF2MSK11_MSK7 _if2msk11.bit._MSK7
#define IF2MSK11_MSK8 _if2msk11.bit._MSK8
#define IF2MSK11_MSK9 _if2msk11.bit._MSK9
#define IF2MSK11_MSK10 _if2msk11.bit._MSK10
#define IF2MSK11_MSK11 _if2msk11.bit._MSK11
#define IF2MSK11_MSK12 _if2msk11.bit._MSK12
#define IF2MSK11_MSK13 _if2msk11.bit._MSK13
#define IF2MSK11_MSK14 _if2msk11.bit._MSK14
#define IF2MSK11_MSK15 _if2msk11.bit._MSK15
__IO_EXTENDED IF2MSK1L1STR _if2msk1l1;  
#define IF2MSK1L1 _if2msk1l1.byte
#define IF2MSK1L1_MSK0 _if2msk1l1.bit._MSK0
#define IF2MSK1L1_MSK1 _if2msk1l1.bit._MSK1
#define IF2MSK1L1_MSK2 _if2msk1l1.bit._MSK2
#define IF2MSK1L1_MSK3 _if2msk1l1.bit._MSK3
#define IF2MSK1L1_MSK4 _if2msk1l1.bit._MSK4
#define IF2MSK1L1_MSK5 _if2msk1l1.bit._MSK5
#define IF2MSK1L1_MSK6 _if2msk1l1.bit._MSK6
#define IF2MSK1L1_MSK7 _if2msk1l1.bit._MSK7
__IO_EXTENDED IF2MSK1H1STR _if2msk1h1;  
#define IF2MSK1H1 _if2msk1h1.byte
#define IF2MSK1H1_MSK8 _if2msk1h1.bit._MSK8
#define IF2MSK1H1_MSK9 _if2msk1h1.bit._MSK9
#define IF2MSK1H1_MSK10 _if2msk1h1.bit._MSK10
#define IF2MSK1H1_MSK11 _if2msk1h1.bit._MSK11
#define IF2MSK1H1_MSK12 _if2msk1h1.bit._MSK12
#define IF2MSK1H1_MSK13 _if2msk1h1.bit._MSK13
#define IF2MSK1H1_MSK14 _if2msk1h1.bit._MSK14
#define IF2MSK1H1_MSK15 _if2msk1h1.bit._MSK15
__IO_EXTENDED IF2MSK21STR _if2msk21;  
#define IF2MSK21 _if2msk21.word
#define IF2MSK21_MSK16 _if2msk21.bit._MSK16
#define IF2MSK21_MSK17 _if2msk21.bit._MSK17
#define IF2MSK21_MSK18 _if2msk21.bit._MSK18
#define IF2MSK21_MSK19 _if2msk21.bit._MSK19
#define IF2MSK21_MSK20 _if2msk21.bit._MSK20
#define IF2MSK21_MSK21 _if2msk21.bit._MSK21
#define IF2MSK21_MSK22 _if2msk21.bit._MSK22
#define IF2MSK21_MSK23 _if2msk21.bit._MSK23
#define IF2MSK21_MSK24 _if2msk21.bit._MSK24
#define IF2MSK21_MSK25 _if2msk21.bit._MSK25
#define IF2MSK21_MSK26 _if2msk21.bit._MSK26
#define IF2MSK21_MSK27 _if2msk21.bit._MSK27
#define IF2MSK21_MSK28 _if2msk21.bit._MSK28
#define IF2MSK21_MDIR _if2msk21.bit._MDIR
#define IF2MSK21_MXTD _if2msk21.bit._MXTD
__IO_EXTENDED IF2MSK2L1STR _if2msk2l1;  
#define IF2MSK2L1 _if2msk2l1.byte
#define IF2MSK2L1_MSK16 _if2msk2l1.bit._MSK16
#define IF2MSK2L1_MSK17 _if2msk2l1.bit._MSK17
#define IF2MSK2L1_MSK18 _if2msk2l1.bit._MSK18
#define IF2MSK2L1_MSK19 _if2msk2l1.bit._MSK19
#define IF2MSK2L1_MSK20 _if2msk2l1.bit._MSK20
#define IF2MSK2L1_MSK21 _if2msk2l1.bit._MSK21
#define IF2MSK2L1_MSK22 _if2msk2l1.bit._MSK22
#define IF2MSK2L1_MSK23 _if2msk2l1.bit._MSK23
__IO_EXTENDED IF2MSK2H1STR _if2msk2h1;  
#define IF2MSK2H1 _if2msk2h1.byte
#define IF2MSK2H1_MSK24 _if2msk2h1.bit._MSK24
#define IF2MSK2H1_MSK25 _if2msk2h1.bit._MSK25
#define IF2MSK2H1_MSK26 _if2msk2h1.bit._MSK26
#define IF2MSK2H1_MSK27 _if2msk2h1.bit._MSK27
#define IF2MSK2H1_MSK28 _if2msk2h1.bit._MSK28
#define IF2MSK2H1_MDIR _if2msk2h1.bit._MDIR
#define IF2MSK2H1_MXTD _if2msk2h1.bit._MXTD
__IO_EXTENDED IF2ARB1STR _if2arb1;  
#define IF2ARB1 _if2arb1.lword
#define IF2ARB1_ID0 _if2arb1.bit._ID0
#define IF2ARB1_ID1 _if2arb1.bit._ID1
#define IF2ARB1_ID2 _if2arb1.bit._ID2
#define IF2ARB1_ID3 _if2arb1.bit._ID3
#define IF2ARB1_ID4 _if2arb1.bit._ID4
#define IF2ARB1_ID5 _if2arb1.bit._ID5
#define IF2ARB1_ID6 _if2arb1.bit._ID6
#define IF2ARB1_ID7 _if2arb1.bit._ID7
#define IF2ARB1_ID8 _if2arb1.bit._ID8
#define IF2ARB1_ID9 _if2arb1.bit._ID9
#define IF2ARB1_ID10 _if2arb1.bit._ID10
#define IF2ARB1_ID11 _if2arb1.bit._ID11
#define IF2ARB1_ID12 _if2arb1.bit._ID12
#define IF2ARB1_ID13 _if2arb1.bit._ID13
#define IF2ARB1_ID14 _if2arb1.bit._ID14
#define IF2ARB1_ID15 _if2arb1.bit._ID15
#define IF2ARB1_ID16 _if2arb1.bit._ID16
#define IF2ARB1_ID17 _if2arb1.bit._ID17
#define IF2ARB1_ID18 _if2arb1.bit._ID18
#define IF2ARB1_ID19 _if2arb1.bit._ID19
#define IF2ARB1_ID20 _if2arb1.bit._ID20
#define IF2ARB1_ID21 _if2arb1.bit._ID21
#define IF2ARB1_ID22 _if2arb1.bit._ID22
#define IF2ARB1_ID23 _if2arb1.bit._ID23
#define IF2ARB1_ID24 _if2arb1.bit._ID24
#define IF2ARB1_ID25 _if2arb1.bit._ID25
#define IF2ARB1_ID26 _if2arb1.bit._ID26
#define IF2ARB1_ID27 _if2arb1.bit._ID27
#define IF2ARB1_ID28 _if2arb1.bit._ID28
#define IF2ARB1_DIR _if2arb1.bit._DIR
#define IF2ARB1_XTD _if2arb1.bit._XTD
#define IF2ARB1_MSGVAL _if2arb1.bit._MSGVAL
#define IF2ARB1_ID _if2arb1.bitc._ID
__IO_EXTENDED IF2ARB11STR _if2arb11;  
#define IF2ARB11 _if2arb11.word
#define IF2ARB11_ID0 _if2arb11.bit._ID0
#define IF2ARB11_ID1 _if2arb11.bit._ID1
#define IF2ARB11_ID2 _if2arb11.bit._ID2
#define IF2ARB11_ID3 _if2arb11.bit._ID3
#define IF2ARB11_ID4 _if2arb11.bit._ID4
#define IF2ARB11_ID5 _if2arb11.bit._ID5
#define IF2ARB11_ID6 _if2arb11.bit._ID6
#define IF2ARB11_ID7 _if2arb11.bit._ID7
#define IF2ARB11_ID8 _if2arb11.bit._ID8
#define IF2ARB11_ID9 _if2arb11.bit._ID9
#define IF2ARB11_ID10 _if2arb11.bit._ID10
#define IF2ARB11_ID11 _if2arb11.bit._ID11
#define IF2ARB11_ID12 _if2arb11.bit._ID12
#define IF2ARB11_ID13 _if2arb11.bit._ID13
#define IF2ARB11_ID14 _if2arb11.bit._ID14
#define IF2ARB11_ID15 _if2arb11.bit._ID15
__IO_EXTENDED IF2ARB1L1STR _if2arb1l1;  
#define IF2ARB1L1 _if2arb1l1.byte
#define IF2ARB1L1_ID0 _if2arb1l1.bit._ID0
#define IF2ARB1L1_ID1 _if2arb1l1.bit._ID1
#define IF2ARB1L1_ID2 _if2arb1l1.bit._ID2
#define IF2ARB1L1_ID3 _if2arb1l1.bit._ID3
#define IF2ARB1L1_ID4 _if2arb1l1.bit._ID4
#define IF2ARB1L1_ID5 _if2arb1l1.bit._ID5
#define IF2ARB1L1_ID6 _if2arb1l1.bit._ID6
#define IF2ARB1L1_ID7 _if2arb1l1.bit._ID7
__IO_EXTENDED IF2ARB1H1STR _if2arb1h1;  
#define IF2ARB1H1 _if2arb1h1.byte
#define IF2ARB1H1_ID8 _if2arb1h1.bit._ID8
#define IF2ARB1H1_ID9 _if2arb1h1.bit._ID9
#define IF2ARB1H1_ID10 _if2arb1h1.bit._ID10
#define IF2ARB1H1_ID11 _if2arb1h1.bit._ID11
#define IF2ARB1H1_ID12 _if2arb1h1.bit._ID12
#define IF2ARB1H1_ID13 _if2arb1h1.bit._ID13
#define IF2ARB1H1_ID14 _if2arb1h1.bit._ID14
#define IF2ARB1H1_ID15 _if2arb1h1.bit._ID15
__IO_EXTENDED IF2ARB21STR _if2arb21;  
#define IF2ARB21 _if2arb21.word
#define IF2ARB21_ID16 _if2arb21.bit._ID16
#define IF2ARB21_ID17 _if2arb21.bit._ID17
#define IF2ARB21_ID18 _if2arb21.bit._ID18
#define IF2ARB21_ID19 _if2arb21.bit._ID19
#define IF2ARB21_ID20 _if2arb21.bit._ID20
#define IF2ARB21_ID21 _if2arb21.bit._ID21
#define IF2ARB21_ID22 _if2arb21.bit._ID22
#define IF2ARB21_ID23 _if2arb21.bit._ID23
#define IF2ARB21_ID24 _if2arb21.bit._ID24
#define IF2ARB21_ID25 _if2arb21.bit._ID25
#define IF2ARB21_ID26 _if2arb21.bit._ID26
#define IF2ARB21_ID27 _if2arb21.bit._ID27
#define IF2ARB21_ID28 _if2arb21.bit._ID28
#define IF2ARB21_DIR _if2arb21.bit._DIR
#define IF2ARB21_XTD _if2arb21.bit._XTD
#define IF2ARB21_MSGVAL _if2arb21.bit._MSGVAL
__IO_EXTENDED IF2ARB2L1STR _if2arb2l1;  
#define IF2ARB2L1 _if2arb2l1.byte
#define IF2ARB2L1_ID16 _if2arb2l1.bit._ID16
#define IF2ARB2L1_ID17 _if2arb2l1.bit._ID17
#define IF2ARB2L1_ID18 _if2arb2l1.bit._ID18
#define IF2ARB2L1_ID19 _if2arb2l1.bit._ID19
#define IF2ARB2L1_ID20 _if2arb2l1.bit._ID20
#define IF2ARB2L1_ID21 _if2arb2l1.bit._ID21
#define IF2ARB2L1_ID22 _if2arb2l1.bit._ID22
#define IF2ARB2L1_ID23 _if2arb2l1.bit._ID23
__IO_EXTENDED IF2ARB2H1STR _if2arb2h1;  
#define IF2ARB2H1 _if2arb2h1.byte
#define IF2ARB2H1_ID24 _if2arb2h1.bit._ID24
#define IF2ARB2H1_ID25 _if2arb2h1.bit._ID25
#define IF2ARB2H1_ID26 _if2arb2h1.bit._ID26
#define IF2ARB2H1_ID27 _if2arb2h1.bit._ID27
#define IF2ARB2H1_ID28 _if2arb2h1.bit._ID28
#define IF2ARB2H1_DIR _if2arb2h1.bit._DIR
#define IF2ARB2H1_XTD _if2arb2h1.bit._XTD
#define IF2ARB2H1_MSGVAL _if2arb2h1.bit._MSGVAL
__IO_EXTENDED IF2MCTR1STR _if2mctr1;  
#define IF2MCTR1 _if2mctr1.word
#define IF2MCTR1_DLC0 _if2mctr1.bit._DLC0
#define IF2MCTR1_DLC1 _if2mctr1.bit._DLC1
#define IF2MCTR1_DLC2 _if2mctr1.bit._DLC2
#define IF2MCTR1_DLC3 _if2mctr1.bit._DLC3
#define IF2MCTR1_EOB _if2mctr1.bit._EOB
#define IF2MCTR1_TXRQST _if2mctr1.bit._TXRQST
#define IF2MCTR1_RMTEN _if2mctr1.bit._RMTEN
#define IF2MCTR1_RXIE _if2mctr1.bit._RXIE
#define IF2MCTR1_TXIE _if2mctr1.bit._TXIE
#define IF2MCTR1_UMASK _if2mctr1.bit._UMASK
#define IF2MCTR1_INTPND _if2mctr1.bit._INTPND
#define IF2MCTR1_MSGLST _if2mctr1.bit._MSGLST
#define IF2MCTR1_NEWDAT _if2mctr1.bit._NEWDAT
#define IF2MCTR1_DLC _if2mctr1.bitc._DLC
__IO_EXTENDED IF2MCTRL1STR _if2mctrl1;  
#define IF2MCTRL1 _if2mctrl1.byte
#define IF2MCTRL1_DLC0 _if2mctrl1.bit._DLC0
#define IF2MCTRL1_DLC1 _if2mctrl1.bit._DLC1
#define IF2MCTRL1_DLC2 _if2mctrl1.bit._DLC2
#define IF2MCTRL1_DLC3 _if2mctrl1.bit._DLC3
#define IF2MCTRL1_EOB _if2mctrl1.bit._EOB
#define IF2MCTRL1_DLC _if2mctrl1.bitc._DLC
__IO_EXTENDED IF2MCTRH1STR _if2mctrh1;  
#define IF2MCTRH1 _if2mctrh1.byte
#define IF2MCTRH1_TXRQST _if2mctrh1.bit._TXRQST
#define IF2MCTRH1_RMTEN _if2mctrh1.bit._RMTEN
#define IF2MCTRH1_RXIE _if2mctrh1.bit._RXIE
#define IF2MCTRH1_TXIE _if2mctrh1.bit._TXIE
#define IF2MCTRH1_UMASK _if2mctrh1.bit._UMASK
#define IF2MCTRH1_INTPND _if2mctrh1.bit._INTPND
#define IF2MCTRH1_MSGLST _if2mctrh1.bit._MSGLST
#define IF2MCTRH1_NEWDAT _if2mctrh1.bit._NEWDAT
__IO_EXTENDED IF2DTA1STR _if2dta1;  
#define IF2DTA1 _if2dta1.lword
__IO_EXTENDED IF2DTA11STR _if2dta11;  
#define IF2DTA11 _if2dta11.word
__IO_EXTENDED IF2DTA1L1STR _if2dta1l1;  
#define IF2DTA1L1 _if2dta1l1.byte
__IO_EXTENDED IF2DTA1H1STR _if2dta1h1;  
#define IF2DTA1H1 _if2dta1h1.byte
__IO_EXTENDED IF2DTA21STR _if2dta21;  
#define IF2DTA21 _if2dta21.word
__IO_EXTENDED IF2DTA2L1STR _if2dta2l1;  
#define IF2DTA2L1 _if2dta2l1.byte
__IO_EXTENDED IF2DTA2H1STR _if2dta2h1;  
#define IF2DTA2H1 _if2dta2h1.byte
__IO_EXTENDED IF2DTB1STR _if2dtb1;  
#define IF2DTB1 _if2dtb1.lword
__IO_EXTENDED IF2DTB11STR _if2dtb11;  
#define IF2DTB11 _if2dtb11.word
__IO_EXTENDED IF2DTB1L1STR _if2dtb1l1;  
#define IF2DTB1L1 _if2dtb1l1.byte
__IO_EXTENDED IF2DTB1H1STR _if2dtb1h1;  
#define IF2DTB1H1 _if2dtb1h1.byte
__IO_EXTENDED IF2DTB21STR _if2dtb21;  
#define IF2DTB21 _if2dtb21.word
__IO_EXTENDED IF2DTB2L1STR _if2dtb2l1;  
#define IF2DTB2L1 _if2dtb2l1.byte
__IO_EXTENDED IF2DTB2H1STR _if2dtb2h1;  
#define IF2DTB2H1 _if2dtb2h1.byte
__IO_EXTENDED TREQR1STR _treqr1;  
#define TREQR1 _treqr1.lword
#define TREQR1_TXRQST1 _treqr1.bit._TXRQST1
#define TREQR1_TXRQST2 _treqr1.bit._TXRQST2
#define TREQR1_TXRQST3 _treqr1.bit._TXRQST3
#define TREQR1_TXRQST4 _treqr1.bit._TXRQST4
#define TREQR1_TXRQST5 _treqr1.bit._TXRQST5
#define TREQR1_TXRQST6 _treqr1.bit._TXRQST6
#define TREQR1_TXRQST7 _treqr1.bit._TXRQST7
#define TREQR1_TXRQST8 _treqr1.bit._TXRQST8
#define TREQR1_TXRQST9 _treqr1.bit._TXRQST9
#define TREQR1_TXRQST10 _treqr1.bit._TXRQST10
#define TREQR1_TXRQST11 _treqr1.bit._TXRQST11
#define TREQR1_TXRQST12 _treqr1.bit._TXRQST12
#define TREQR1_TXRQST13 _treqr1.bit._TXRQST13
#define TREQR1_TXRQST14 _treqr1.bit._TXRQST14
#define TREQR1_TXRQST15 _treqr1.bit._TXRQST15
#define TREQR1_TXRQST16 _treqr1.bit._TXRQST16
#define TREQR1_TXRQST17 _treqr1.bit._TXRQST17
#define TREQR1_TXRQST18 _treqr1.bit._TXRQST18
#define TREQR1_TXRQST19 _treqr1.bit._TXRQST19
#define TREQR1_TXRQST20 _treqr1.bit._TXRQST20
#define TREQR1_TXRQST21 _treqr1.bit._TXRQST21
#define TREQR1_TXRQST22 _treqr1.bit._TXRQST22
#define TREQR1_TXRQST23 _treqr1.bit._TXRQST23
#define TREQR1_TXRQST24 _treqr1.bit._TXRQST24
#define TREQR1_TXRQST25 _treqr1.bit._TXRQST25
#define TREQR1_TXRQST26 _treqr1.bit._TXRQST26
#define TREQR1_TXRQST27 _treqr1.bit._TXRQST27
#define TREQR1_TXRQST28 _treqr1.bit._TXRQST28
#define TREQR1_TXRQST29 _treqr1.bit._TXRQST29
#define TREQR1_TXRQST30 _treqr1.bit._TXRQST30
#define TREQR1_TXRQST31 _treqr1.bit._TXRQST31
#define TREQR1_TXRQST32 _treqr1.bit._TXRQST32
#define TREQR1_TXRQST _treqr1.bitc._TXRQST
__IO_EXTENDED TREQR11STR _treqr11;  
#define TREQR11 _treqr11.word
#define TREQR11_TXRQST1 _treqr11.bit._TXRQST1
#define TREQR11_TXRQST2 _treqr11.bit._TXRQST2
#define TREQR11_TXRQST3 _treqr11.bit._TXRQST3
#define TREQR11_TXRQST4 _treqr11.bit._TXRQST4
#define TREQR11_TXRQST5 _treqr11.bit._TXRQST5
#define TREQR11_TXRQST6 _treqr11.bit._TXRQST6
#define TREQR11_TXRQST7 _treqr11.bit._TXRQST7
#define TREQR11_TXRQST8 _treqr11.bit._TXRQST8
#define TREQR11_TXRQST9 _treqr11.bit._TXRQST9
#define TREQR11_TXRQST10 _treqr11.bit._TXRQST10
#define TREQR11_TXRQST11 _treqr11.bit._TXRQST11
#define TREQR11_TXRQST12 _treqr11.bit._TXRQST12
#define TREQR11_TXRQST13 _treqr11.bit._TXRQST13
#define TREQR11_TXRQST14 _treqr11.bit._TXRQST14
#define TREQR11_TXRQST15 _treqr11.bit._TXRQST15
#define TREQR11_TXRQST16 _treqr11.bit._TXRQST16
__IO_EXTENDED TREQR1L1STR _treqr1l1;  
#define TREQR1L1 _treqr1l1.byte
#define TREQR1L1_TXRQST1 _treqr1l1.bit._TXRQST1
#define TREQR1L1_TXRQST2 _treqr1l1.bit._TXRQST2
#define TREQR1L1_TXRQST3 _treqr1l1.bit._TXRQST3
#define TREQR1L1_TXRQST4 _treqr1l1.bit._TXRQST4
#define TREQR1L1_TXRQST5 _treqr1l1.bit._TXRQST5
#define TREQR1L1_TXRQST6 _treqr1l1.bit._TXRQST6
#define TREQR1L1_TXRQST7 _treqr1l1.bit._TXRQST7
#define TREQR1L1_TXRQST8 _treqr1l1.bit._TXRQST8
__IO_EXTENDED TREQR1H1STR _treqr1h1;  
#define TREQR1H1 _treqr1h1.byte
#define TREQR1H1_TXRQST9 _treqr1h1.bit._TXRQST9
#define TREQR1H1_TXRQST10 _treqr1h1.bit._TXRQST10
#define TREQR1H1_TXRQST11 _treqr1h1.bit._TXRQST11
#define TREQR1H1_TXRQST12 _treqr1h1.bit._TXRQST12
#define TREQR1H1_TXRQST13 _treqr1h1.bit._TXRQST13
#define TREQR1H1_TXRQST14 _treqr1h1.bit._TXRQST14
#define TREQR1H1_TXRQST15 _treqr1h1.bit._TXRQST15
#define TREQR1H1_TXRQST16 _treqr1h1.bit._TXRQST16
__IO_EXTENDED TREQR21STR _treqr21;  
#define TREQR21 _treqr21.word
#define TREQR21_TXRQST17 _treqr21.bit._TXRQST17
#define TREQR21_TXRQST18 _treqr21.bit._TXRQST18
#define TREQR21_TXRQST19 _treqr21.bit._TXRQST19
#define TREQR21_TXRQST20 _treqr21.bit._TXRQST20
#define TREQR21_TXRQST21 _treqr21.bit._TXRQST21
#define TREQR21_TXRQST22 _treqr21.bit._TXRQST22
#define TREQR21_TXRQST23 _treqr21.bit._TXRQST23
#define TREQR21_TXRQST24 _treqr21.bit._TXRQST24
#define TREQR21_TXRQST25 _treqr21.bit._TXRQST25
#define TREQR21_TXRQST26 _treqr21.bit._TXRQST26
#define TREQR21_TXRQST27 _treqr21.bit._TXRQST27
#define TREQR21_TXRQST28 _treqr21.bit._TXRQST28
#define TREQR21_TXRQST29 _treqr21.bit._TXRQST29
#define TREQR21_TXRQST30 _treqr21.bit._TXRQST30
#define TREQR21_TXRQST31 _treqr21.bit._TXRQST31
#define TREQR21_TXRQST32 _treqr21.bit._TXRQST32
__IO_EXTENDED TREQR2L1STR _treqr2l1;  
#define TREQR2L1 _treqr2l1.byte
#define TREQR2L1_TXRQST17 _treqr2l1.bit._TXRQST17
#define TREQR2L1_TXRQST18 _treqr2l1.bit._TXRQST18
#define TREQR2L1_TXRQST19 _treqr2l1.bit._TXRQST19
#define TREQR2L1_TXRQST20 _treqr2l1.bit._TXRQST20
#define TREQR2L1_TXRQST21 _treqr2l1.bit._TXRQST21
#define TREQR2L1_TXRQST22 _treqr2l1.bit._TXRQST22
#define TREQR2L1_TXRQST23 _treqr2l1.bit._TXRQST23
#define TREQR2L1_TXRQST24 _treqr2l1.bit._TXRQST24
__IO_EXTENDED TREQR2H1STR _treqr2h1;  
#define TREQR2H1 _treqr2h1.byte
#define TREQR2H1_TXRQST25 _treqr2h1.bit._TXRQST25
#define TREQR2H1_TXRQST26 _treqr2h1.bit._TXRQST26
#define TREQR2H1_TXRQST27 _treqr2h1.bit._TXRQST27
#define TREQR2H1_TXRQST28 _treqr2h1.bit._TXRQST28
#define TREQR2H1_TXRQST29 _treqr2h1.bit._TXRQST29
#define TREQR2H1_TXRQST30 _treqr2h1.bit._TXRQST30
#define TREQR2H1_TXRQST31 _treqr2h1.bit._TXRQST31
#define TREQR2H1_TXRQST32 _treqr2h1.bit._TXRQST32
__IO_EXTENDED NEWDT1STR _newdt1;  
#define NEWDT1 _newdt1.lword
#define NEWDT1_NEWDAT1 _newdt1.bit._NEWDAT1
#define NEWDT1_NEWDAT2 _newdt1.bit._NEWDAT2
#define NEWDT1_NEWDAT3 _newdt1.bit._NEWDAT3
#define NEWDT1_NEWDAT4 _newdt1.bit._NEWDAT4
#define NEWDT1_NEWDAT5 _newdt1.bit._NEWDAT5
#define NEWDT1_NEWDAT6 _newdt1.bit._NEWDAT6
#define NEWDT1_NEWDAT7 _newdt1.bit._NEWDAT7
#define NEWDT1_NEWDAT8 _newdt1.bit._NEWDAT8
#define NEWDT1_NEWDAT9 _newdt1.bit._NEWDAT9
#define NEWDT1_NEWDAT10 _newdt1.bit._NEWDAT10
#define NEWDT1_NEWDAT11 _newdt1.bit._NEWDAT11
#define NEWDT1_NEWDAT12 _newdt1.bit._NEWDAT12
#define NEWDT1_NEWDAT13 _newdt1.bit._NEWDAT13
#define NEWDT1_NEWDAT14 _newdt1.bit._NEWDAT14
#define NEWDT1_NEWDAT15 _newdt1.bit._NEWDAT15
#define NEWDT1_NEWDAT16 _newdt1.bit._NEWDAT16
#define NEWDT1_NEWDAT17 _newdt1.bit._NEWDAT17
#define NEWDT1_NEWDAT18 _newdt1.bit._NEWDAT18
#define NEWDT1_NEWDAT19 _newdt1.bit._NEWDAT19
#define NEWDT1_NEWDAT20 _newdt1.bit._NEWDAT20
#define NEWDT1_NEWDAT21 _newdt1.bit._NEWDAT21
#define NEWDT1_NEWDAT22 _newdt1.bit._NEWDAT22
#define NEWDT1_NEWDAT23 _newdt1.bit._NEWDAT23
#define NEWDT1_NEWDAT24 _newdt1.bit._NEWDAT24
#define NEWDT1_NEWDAT25 _newdt1.bit._NEWDAT25
#define NEWDT1_NEWDAT26 _newdt1.bit._NEWDAT26
#define NEWDT1_NEWDAT27 _newdt1.bit._NEWDAT27
#define NEWDT1_NEWDAT28 _newdt1.bit._NEWDAT28
#define NEWDT1_NEWDAT29 _newdt1.bit._NEWDAT29
#define NEWDT1_NEWDAT30 _newdt1.bit._NEWDAT30
#define NEWDT1_NEWDAT31 _newdt1.bit._NEWDAT31
#define NEWDT1_NEWDAT32 _newdt1.bit._NEWDAT32
#define NEWDT1_NEWDAT _newdt1.bitc._NEWDAT
__IO_EXTENDED NEWDT11STR _newdt11;  
#define NEWDT11 _newdt11.word
#define NEWDT11_NEWDAT1 _newdt11.bit._NEWDAT1
#define NEWDT11_NEWDAT2 _newdt11.bit._NEWDAT2
#define NEWDT11_NEWDAT3 _newdt11.bit._NEWDAT3
#define NEWDT11_NEWDAT4 _newdt11.bit._NEWDAT4
#define NEWDT11_NEWDAT5 _newdt11.bit._NEWDAT5
#define NEWDT11_NEWDAT6 _newdt11.bit._NEWDAT6
#define NEWDT11_NEWDAT7 _newdt11.bit._NEWDAT7
#define NEWDT11_NEWDAT8 _newdt11.bit._NEWDAT8
#define NEWDT11_NEWDAT9 _newdt11.bit._NEWDAT9
#define NEWDT11_NEWDAT10 _newdt11.bit._NEWDAT10
#define NEWDT11_NEWDAT11 _newdt11.bit._NEWDAT11
#define NEWDT11_NEWDAT12 _newdt11.bit._NEWDAT12
#define NEWDT11_NEWDAT13 _newdt11.bit._NEWDAT13
#define NEWDT11_NEWDAT14 _newdt11.bit._NEWDAT14
#define NEWDT11_NEWDAT15 _newdt11.bit._NEWDAT15
#define NEWDT11_NEWDAT16 _newdt11.bit._NEWDAT16
__IO_EXTENDED NEWDT1L1STR _newdt1l1;  
#define NEWDT1L1 _newdt1l1.byte
#define NEWDT1L1_NEWDAT1 _newdt1l1.bit._NEWDAT1
#define NEWDT1L1_NEWDAT2 _newdt1l1.bit._NEWDAT2
#define NEWDT1L1_NEWDAT3 _newdt1l1.bit._NEWDAT3
#define NEWDT1L1_NEWDAT4 _newdt1l1.bit._NEWDAT4
#define NEWDT1L1_NEWDAT5 _newdt1l1.bit._NEWDAT5
#define NEWDT1L1_NEWDAT6 _newdt1l1.bit._NEWDAT6
#define NEWDT1L1_NEWDAT7 _newdt1l1.bit._NEWDAT7
#define NEWDT1L1_NEWDAT8 _newdt1l1.bit._NEWDAT8
__IO_EXTENDED NEWDT1H1STR _newdt1h1;  
#define NEWDT1H1 _newdt1h1.byte
#define NEWDT1H1_NEWDAT9 _newdt1h1.bit._NEWDAT9
#define NEWDT1H1_NEWDAT10 _newdt1h1.bit._NEWDAT10
#define NEWDT1H1_NEWDAT11 _newdt1h1.bit._NEWDAT11
#define NEWDT1H1_NEWDAT12 _newdt1h1.bit._NEWDAT12
#define NEWDT1H1_NEWDAT13 _newdt1h1.bit._NEWDAT13
#define NEWDT1H1_NEWDAT14 _newdt1h1.bit._NEWDAT14
#define NEWDT1H1_NEWDAT15 _newdt1h1.bit._NEWDAT15
#define NEWDT1H1_NEWDAT16 _newdt1h1.bit._NEWDAT16
__IO_EXTENDED NEWDT21STR _newdt21;  
#define NEWDT21 _newdt21.word
#define NEWDT21_NEWDAT17 _newdt21.bit._NEWDAT17
#define NEWDT21_NEWDAT18 _newdt21.bit._NEWDAT18
#define NEWDT21_NEWDAT19 _newdt21.bit._NEWDAT19
#define NEWDT21_NEWDAT20 _newdt21.bit._NEWDAT20
#define NEWDT21_NEWDAT21 _newdt21.bit._NEWDAT21
#define NEWDT21_NEWDAT22 _newdt21.bit._NEWDAT22
#define NEWDT21_NEWDAT23 _newdt21.bit._NEWDAT23
#define NEWDT21_NEWDAT24 _newdt21.bit._NEWDAT24
#define NEWDT21_NEWDAT25 _newdt21.bit._NEWDAT25
#define NEWDT21_NEWDAT26 _newdt21.bit._NEWDAT26
#define NEWDT21_NEWDAT27 _newdt21.bit._NEWDAT27
#define NEWDT21_NEWDAT28 _newdt21.bit._NEWDAT28
#define NEWDT21_NEWDAT29 _newdt21.bit._NEWDAT29
#define NEWDT21_NEWDAT30 _newdt21.bit._NEWDAT30
#define NEWDT21_NEWDAT31 _newdt21.bit._NEWDAT31
#define NEWDT21_NEWDAT32 _newdt21.bit._NEWDAT32
__IO_EXTENDED NEWDT2L1STR _newdt2l1;  
#define NEWDT2L1 _newdt2l1.byte
#define NEWDT2L1_NEWDAT17 _newdt2l1.bit._NEWDAT17
#define NEWDT2L1_NEWDAT18 _newdt2l1.bit._NEWDAT18
#define NEWDT2L1_NEWDAT19 _newdt2l1.bit._NEWDAT19
#define NEWDT2L1_NEWDAT20 _newdt2l1.bit._NEWDAT20
#define NEWDT2L1_NEWDAT21 _newdt2l1.bit._NEWDAT21
#define NEWDT2L1_NEWDAT22 _newdt2l1.bit._NEWDAT22
#define NEWDT2L1_NEWDAT23 _newdt2l1.bit._NEWDAT23
#define NEWDT2L1_NEWDAT24 _newdt2l1.bit._NEWDAT24
__IO_EXTENDED NEWDT2H1STR _newdt2h1;  
#define NEWDT2H1 _newdt2h1.byte
#define NEWDT2H1_NEWDAT25 _newdt2h1.bit._NEWDAT25
#define NEWDT2H1_NEWDAT26 _newdt2h1.bit._NEWDAT26
#define NEWDT2H1_NEWDAT27 _newdt2h1.bit._NEWDAT27
#define NEWDT2H1_NEWDAT28 _newdt2h1.bit._NEWDAT28
#define NEWDT2H1_NEWDAT29 _newdt2h1.bit._NEWDAT29
#define NEWDT2H1_NEWDAT30 _newdt2h1.bit._NEWDAT30
#define NEWDT2H1_NEWDAT31 _newdt2h1.bit._NEWDAT31
#define NEWDT2H1_NEWDAT32 _newdt2h1.bit._NEWDAT32
__IO_EXTENDED INTPND1STR _intpnd1;  
#define INTPND1 _intpnd1.lword
#define INTPND1_INTPND1 _intpnd1.bit._INTPND1
#define INTPND1_INTPND2 _intpnd1.bit._INTPND2
#define INTPND1_INTPND3 _intpnd1.bit._INTPND3
#define INTPND1_INTPND4 _intpnd1.bit._INTPND4
#define INTPND1_INTPND5 _intpnd1.bit._INTPND5
#define INTPND1_INTPND6 _intpnd1.bit._INTPND6
#define INTPND1_INTPND7 _intpnd1.bit._INTPND7
#define INTPND1_INTPND8 _intpnd1.bit._INTPND8
#define INTPND1_INTPND9 _intpnd1.bit._INTPND9
#define INTPND1_INTPND10 _intpnd1.bit._INTPND10
#define INTPND1_INTPND11 _intpnd1.bit._INTPND11
#define INTPND1_INTPND12 _intpnd1.bit._INTPND12
#define INTPND1_INTPND13 _intpnd1.bit._INTPND13
#define INTPND1_INTPND14 _intpnd1.bit._INTPND14
#define INTPND1_INTPND15 _intpnd1.bit._INTPND15
#define INTPND1_INTPND16 _intpnd1.bit._INTPND16
#define INTPND1_INTPND17 _intpnd1.bit._INTPND17
#define INTPND1_INTPND18 _intpnd1.bit._INTPND18
#define INTPND1_INTPND19 _intpnd1.bit._INTPND19
#define INTPND1_INTPND20 _intpnd1.bit._INTPND20
#define INTPND1_INTPND21 _intpnd1.bit._INTPND21
#define INTPND1_INTPND22 _intpnd1.bit._INTPND22
#define INTPND1_INTPND23 _intpnd1.bit._INTPND23
#define INTPND1_INTPND24 _intpnd1.bit._INTPND24
#define INTPND1_INTPND25 _intpnd1.bit._INTPND25
#define INTPND1_INTPND26 _intpnd1.bit._INTPND26
#define INTPND1_INTPND27 _intpnd1.bit._INTPND27
#define INTPND1_INTPND28 _intpnd1.bit._INTPND28
#define INTPND1_INTPND29 _intpnd1.bit._INTPND29
#define INTPND1_INTPND30 _intpnd1.bit._INTPND30
#define INTPND1_INTPND31 _intpnd1.bit._INTPND31
#define INTPND1_INTPND32 _intpnd1.bit._INTPND32
#define INTPND1_INTPND _intpnd1.bitc._INTPND
__IO_EXTENDED INTPND11STR _intpnd11;  
#define INTPND11 _intpnd11.word
#define INTPND11_INTPND1 _intpnd11.bit._INTPND1
#define INTPND11_INTPND2 _intpnd11.bit._INTPND2
#define INTPND11_INTPND3 _intpnd11.bit._INTPND3
#define INTPND11_INTPND4 _intpnd11.bit._INTPND4
#define INTPND11_INTPND5 _intpnd11.bit._INTPND5
#define INTPND11_INTPND6 _intpnd11.bit._INTPND6
#define INTPND11_INTPND7 _intpnd11.bit._INTPND7
#define INTPND11_INTPND8 _intpnd11.bit._INTPND8
#define INTPND11_INTPND9 _intpnd11.bit._INTPND9
#define INTPND11_INTPND10 _intpnd11.bit._INTPND10
#define INTPND11_INTPND11 _intpnd11.bit._INTPND11
#define INTPND11_INTPND12 _intpnd11.bit._INTPND12
#define INTPND11_INTPND13 _intpnd11.bit._INTPND13
#define INTPND11_INTPND14 _intpnd11.bit._INTPND14
#define INTPND11_INTPND15 _intpnd11.bit._INTPND15
#define INTPND11_INTPND16 _intpnd11.bit._INTPND16
__IO_EXTENDED INTPND1L1STR _intpnd1l1;  
#define INTPND1L1 _intpnd1l1.byte
#define INTPND1L1_INTPND1 _intpnd1l1.bit._INTPND1
#define INTPND1L1_INTPND2 _intpnd1l1.bit._INTPND2
#define INTPND1L1_INTPND3 _intpnd1l1.bit._INTPND3
#define INTPND1L1_INTPND4 _intpnd1l1.bit._INTPND4
#define INTPND1L1_INTPND5 _intpnd1l1.bit._INTPND5
#define INTPND1L1_INTPND6 _intpnd1l1.bit._INTPND6
#define INTPND1L1_INTPND7 _intpnd1l1.bit._INTPND7
#define INTPND1L1_INTPND8 _intpnd1l1.bit._INTPND8
__IO_EXTENDED INTPND1H1STR _intpnd1h1;  
#define INTPND1H1 _intpnd1h1.byte
#define INTPND1H1_INTPND9 _intpnd1h1.bit._INTPND9
#define INTPND1H1_INTPND10 _intpnd1h1.bit._INTPND10
#define INTPND1H1_INTPND11 _intpnd1h1.bit._INTPND11
#define INTPND1H1_INTPND12 _intpnd1h1.bit._INTPND12
#define INTPND1H1_INTPND13 _intpnd1h1.bit._INTPND13
#define INTPND1H1_INTPND14 _intpnd1h1.bit._INTPND14
#define INTPND1H1_INTPND15 _intpnd1h1.bit._INTPND15
#define INTPND1H1_INTPND16 _intpnd1h1.bit._INTPND16
__IO_EXTENDED INTPND21STR _intpnd21;  
#define INTPND21 _intpnd21.word
#define INTPND21_INTPND17 _intpnd21.bit._INTPND17
#define INTPND21_INTPND18 _intpnd21.bit._INTPND18
#define INTPND21_INTPND19 _intpnd21.bit._INTPND19
#define INTPND21_INTPND20 _intpnd21.bit._INTPND20
#define INTPND21_INTPND21 _intpnd21.bit._INTPND21
#define INTPND21_INTPND22 _intpnd21.bit._INTPND22
#define INTPND21_INTPND23 _intpnd21.bit._INTPND23
#define INTPND21_INTPND24 _intpnd21.bit._INTPND24
#define INTPND21_INTPND25 _intpnd21.bit._INTPND25
#define INTPND21_INTPND26 _intpnd21.bit._INTPND26
#define INTPND21_INTPND27 _intpnd21.bit._INTPND27
#define INTPND21_INTPND28 _intpnd21.bit._INTPND28
#define INTPND21_INTPND29 _intpnd21.bit._INTPND29
#define INTPND21_INTPND30 _intpnd21.bit._INTPND30
#define INTPND21_INTPND31 _intpnd21.bit._INTPND31
#define INTPND21_INTPND32 _intpnd21.bit._INTPND32
__IO_EXTENDED INTPND2L1STR _intpnd2l1;  
#define INTPND2L1 _intpnd2l1.byte
#define INTPND2L1_INTPND17 _intpnd2l1.bit._INTPND17
#define INTPND2L1_INTPND18 _intpnd2l1.bit._INTPND18
#define INTPND2L1_INTPND19 _intpnd2l1.bit._INTPND19
#define INTPND2L1_INTPND20 _intpnd2l1.bit._INTPND20
#define INTPND2L1_INTPND21 _intpnd2l1.bit._INTPND21
#define INTPND2L1_INTPND22 _intpnd2l1.bit._INTPND22
#define INTPND2L1_INTPND23 _intpnd2l1.bit._INTPND23
#define INTPND2L1_INTPND24 _intpnd2l1.bit._INTPND24
__IO_EXTENDED INTPND2H1STR _intpnd2h1;  
#define INTPND2H1 _intpnd2h1.byte
#define INTPND2H1_INTPND25 _intpnd2h1.bit._INTPND25
#define INTPND2H1_INTPND26 _intpnd2h1.bit._INTPND26
#define INTPND2H1_INTPND27 _intpnd2h1.bit._INTPND27
#define INTPND2H1_INTPND28 _intpnd2h1.bit._INTPND28
#define INTPND2H1_INTPND29 _intpnd2h1.bit._INTPND29
#define INTPND2H1_INTPND30 _intpnd2h1.bit._INTPND30
#define INTPND2H1_INTPND31 _intpnd2h1.bit._INTPND31
#define INTPND2H1_INTPND32 _intpnd2h1.bit._INTPND32
__IO_EXTENDED MSGVAL1STR _msgval1;  
#define MSGVAL1 _msgval1.lword
#define MSGVAL1_MSGVAL1 _msgval1.bit._MSGVAL1
#define MSGVAL1_MSGVAL2 _msgval1.bit._MSGVAL2
#define MSGVAL1_MSGVAL3 _msgval1.bit._MSGVAL3
#define MSGVAL1_MSGVAL4 _msgval1.bit._MSGVAL4
#define MSGVAL1_MSGVAL5 _msgval1.bit._MSGVAL5
#define MSGVAL1_MSGVAL6 _msgval1.bit._MSGVAL6
#define MSGVAL1_MSGVAL7 _msgval1.bit._MSGVAL7
#define MSGVAL1_MSGVAL8 _msgval1.bit._MSGVAL8
#define MSGVAL1_MSGVAL9 _msgval1.bit._MSGVAL9
#define MSGVAL1_MSGVAL10 _msgval1.bit._MSGVAL10
#define MSGVAL1_MSGVAL11 _msgval1.bit._MSGVAL11
#define MSGVAL1_MSGVAL12 _msgval1.bit._MSGVAL12
#define MSGVAL1_MSGVAL13 _msgval1.bit._MSGVAL13
#define MSGVAL1_MSGVAL14 _msgval1.bit._MSGVAL14
#define MSGVAL1_MSGVAL15 _msgval1.bit._MSGVAL15
#define MSGVAL1_MSGVAL16 _msgval1.bit._MSGVAL16
#define MSGVAL1_MSGVAL17 _msgval1.bit._MSGVAL17
#define MSGVAL1_MSGVAL18 _msgval1.bit._MSGVAL18
#define MSGVAL1_MSGVAL19 _msgval1.bit._MSGVAL19
#define MSGVAL1_MSGVAL20 _msgval1.bit._MSGVAL20
#define MSGVAL1_MSGVAL21 _msgval1.bit._MSGVAL21
#define MSGVAL1_MSGVAL22 _msgval1.bit._MSGVAL22
#define MSGVAL1_MSGVAL23 _msgval1.bit._MSGVAL23
#define MSGVAL1_MSGVAL24 _msgval1.bit._MSGVAL24
#define MSGVAL1_MSGVAL25 _msgval1.bit._MSGVAL25
#define MSGVAL1_MSGVAL26 _msgval1.bit._MSGVAL26
#define MSGVAL1_MSGVAL27 _msgval1.bit._MSGVAL27
#define MSGVAL1_MSGVAL28 _msgval1.bit._MSGVAL28
#define MSGVAL1_MSGVAL29 _msgval1.bit._MSGVAL29
#define MSGVAL1_MSGVAL30 _msgval1.bit._MSGVAL30
#define MSGVAL1_MSGVAL31 _msgval1.bit._MSGVAL31
#define MSGVAL1_MSGVAL32 _msgval1.bit._MSGVAL32
#define MSGVAL1_MSGVAL _msgval1.bitc._MSGVAL
__IO_EXTENDED MSGVAL11STR _msgval11;  
#define MSGVAL11 _msgval11.word
#define MSGVAL11_MSGVAL1 _msgval11.bit._MSGVAL1
#define MSGVAL11_MSGVAL2 _msgval11.bit._MSGVAL2
#define MSGVAL11_MSGVAL3 _msgval11.bit._MSGVAL3
#define MSGVAL11_MSGVAL4 _msgval11.bit._MSGVAL4
#define MSGVAL11_MSGVAL5 _msgval11.bit._MSGVAL5
#define MSGVAL11_MSGVAL6 _msgval11.bit._MSGVAL6
#define MSGVAL11_MSGVAL7 _msgval11.bit._MSGVAL7
#define MSGVAL11_MSGVAL8 _msgval11.bit._MSGVAL8
#define MSGVAL11_MSGVAL9 _msgval11.bit._MSGVAL9
#define MSGVAL11_MSGVAL10 _msgval11.bit._MSGVAL10
#define MSGVAL11_MSGVAL11 _msgval11.bit._MSGVAL11
#define MSGVAL11_MSGVAL12 _msgval11.bit._MSGVAL12
#define MSGVAL11_MSGVAL13 _msgval11.bit._MSGVAL13
#define MSGVAL11_MSGVAL14 _msgval11.bit._MSGVAL14
#define MSGVAL11_MSGVAL15 _msgval11.bit._MSGVAL15
#define MSGVAL11_MSGVAL16 _msgval11.bit._MSGVAL16
__IO_EXTENDED MSGVAL1L1STR _msgval1l1;  
#define MSGVAL1L1 _msgval1l1.byte
#define MSGVAL1L1_MSGVAL1 _msgval1l1.bit._MSGVAL1
#define MSGVAL1L1_MSGVAL2 _msgval1l1.bit._MSGVAL2
#define MSGVAL1L1_MSGVAL3 _msgval1l1.bit._MSGVAL3
#define MSGVAL1L1_MSGVAL4 _msgval1l1.bit._MSGVAL4
#define MSGVAL1L1_MSGVAL5 _msgval1l1.bit._MSGVAL5
#define MSGVAL1L1_MSGVAL6 _msgval1l1.bit._MSGVAL6
#define MSGVAL1L1_MSGVAL7 _msgval1l1.bit._MSGVAL7
#define MSGVAL1L1_MSGVAL8 _msgval1l1.bit._MSGVAL8
__IO_EXTENDED MSGVAL1H1STR _msgval1h1;  
#define MSGVAL1H1 _msgval1h1.byte
#define MSGVAL1H1_MSGVAL9 _msgval1h1.bit._MSGVAL9
#define MSGVAL1H1_MSGVAL10 _msgval1h1.bit._MSGVAL10
#define MSGVAL1H1_MSGVAL11 _msgval1h1.bit._MSGVAL11
#define MSGVAL1H1_MSGVAL12 _msgval1h1.bit._MSGVAL12
#define MSGVAL1H1_MSGVAL13 _msgval1h1.bit._MSGVAL13
#define MSGVAL1H1_MSGVAL14 _msgval1h1.bit._MSGVAL14
#define MSGVAL1H1_MSGVAL15 _msgval1h1.bit._MSGVAL15
#define MSGVAL1H1_MSGVAL16 _msgval1h1.bit._MSGVAL16
__IO_EXTENDED MSGVAL21STR _msgval21;  
#define MSGVAL21 _msgval21.word
#define MSGVAL21_MSGVAL17 _msgval21.bit._MSGVAL17
#define MSGVAL21_MSGVAL18 _msgval21.bit._MSGVAL18
#define MSGVAL21_MSGVAL19 _msgval21.bit._MSGVAL19
#define MSGVAL21_MSGVAL20 _msgval21.bit._MSGVAL20
#define MSGVAL21_MSGVAL21 _msgval21.bit._MSGVAL21
#define MSGVAL21_MSGVAL22 _msgval21.bit._MSGVAL22
#define MSGVAL21_MSGVAL23 _msgval21.bit._MSGVAL23
#define MSGVAL21_MSGVAL24 _msgval21.bit._MSGVAL24
#define MSGVAL21_MSGVAL25 _msgval21.bit._MSGVAL25
#define MSGVAL21_MSGVAL26 _msgval21.bit._MSGVAL26
#define MSGVAL21_MSGVAL27 _msgval21.bit._MSGVAL27
#define MSGVAL21_MSGVAL28 _msgval21.bit._MSGVAL28
#define MSGVAL21_MSGVAL29 _msgval21.bit._MSGVAL29
#define MSGVAL21_MSGVAL30 _msgval21.bit._MSGVAL30
#define MSGVAL21_MSGVAL31 _msgval21.bit._MSGVAL31
#define MSGVAL21_MSGVAL32 _msgval21.bit._MSGVAL32
__IO_EXTENDED MSGVAL2L1STR _msgval2l1;  
#define MSGVAL2L1 _msgval2l1.byte
#define MSGVAL2L1_MSGVAL17 _msgval2l1.bit._MSGVAL17
#define MSGVAL2L1_MSGVAL18 _msgval2l1.bit._MSGVAL18
#define MSGVAL2L1_MSGVAL19 _msgval2l1.bit._MSGVAL19
#define MSGVAL2L1_MSGVAL20 _msgval2l1.bit._MSGVAL20
#define MSGVAL2L1_MSGVAL21 _msgval2l1.bit._MSGVAL21
#define MSGVAL2L1_MSGVAL22 _msgval2l1.bit._MSGVAL22
#define MSGVAL2L1_MSGVAL23 _msgval2l1.bit._MSGVAL23
#define MSGVAL2L1_MSGVAL24 _msgval2l1.bit._MSGVAL24
__IO_EXTENDED MSGVAL2H1STR _msgval2h1;  
#define MSGVAL2H1 _msgval2h1.byte
#define MSGVAL2H1_MSGVAL25 _msgval2h1.bit._MSGVAL25
#define MSGVAL2H1_MSGVAL26 _msgval2h1.bit._MSGVAL26
#define MSGVAL2H1_MSGVAL27 _msgval2h1.bit._MSGVAL27
#define MSGVAL2H1_MSGVAL28 _msgval2h1.bit._MSGVAL28
#define MSGVAL2H1_MSGVAL29 _msgval2h1.bit._MSGVAL29
#define MSGVAL2H1_MSGVAL30 _msgval2h1.bit._MSGVAL30
#define MSGVAL2H1_MSGVAL31 _msgval2h1.bit._MSGVAL31
#define MSGVAL2H1_MSGVAL32 _msgval2h1.bit._MSGVAL32
__IO_EXTENDED COER1STR _coer1;  
#define COER1 _coer1.byte
#define COER1_OE _coer1.bit._OE
#  undef ___IOWIDTH
#endif                   /* __MB90XXX_H */
