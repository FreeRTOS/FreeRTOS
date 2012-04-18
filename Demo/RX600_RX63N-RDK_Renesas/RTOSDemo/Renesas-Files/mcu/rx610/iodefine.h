/************************************************************************
*
* Device     : RX/RX600/RX610
*
* File Name  : ioedfine.h
*
* Abstract   : Definition of I/O Register. MSB
*
* History    : 1.02 (2009-09-10)  [Hardware Manual Revision : 0.12]
*            : 1.03 (2010-03-04)  [Hardware Manual Revision : 1.00]
*            : 1.04 (2010-04-16)  [Hardware Manual Revision : 1.00]
*            : 4.10 (2010-08-21)  [Hardware Manual Revision : 1.00]
*
* NOTE       : THIS IS A TYPICAL EXAMPLE.
*
*  Copyright (C) 2010 Renesas Electronics Corporation and
*  Renesas Solutions Corp. All rights reserved.
*
************************************************************************/
/********************************************************************************/
/*                                                                              */
/*  DESCRIPTION : Definition of ICU Register                                    */
/*  CPU TYPE    : RX610                                                         */
/*                                                                              */
/*  Usage : IR,ISELR,IER,IPR of ICU Register                                    */
/*     The following IR, ISEL, IEN, IPR macro functions simplify usage.         */
/*     The bit access operation is "Bit_Name(interrupt source,name)".           */
/*     A part of the name can be omitted.                                       */
/*     for example :                                                            */
/*       IR(TPU0,TGI0A) = 0;     expands to :                                   */
/*         ICU.IR[104].BIT.IR = 0;                                              */
/*                                                                              */
/*       ISEL(ICU,IRQ0) = 1;     expands to :                                   */
/*         ICU.ISELR[64].BIT.ISEL = 1;                                          */
/*                                                                              */
/*       IEN(CMT0,CMI0) = 1;     expands to :                                   */
/*         ICU.IER[0x03].BIT.IEN4 = 1;                                          */
/*                                                                              */
/*       IPR(TPU0,TGI0A) = 2;    expands to :                                   */
/*       IPR(TPU0,TGI  ) = 2;    // TGI0A,TGI0B,TGI0C,TGI0D share IPR level.    */
/*         ICU.IPR[0x4C].BIT.IPR = 2;                                           */
/*                                                                              */
/*       IPR(SCI0,ERI0) = 3;     expands to :                                   */
/*       IPR(SCI0,    ) = 3;     // SCI0 uses single IPR for all sources.       */
/*         ICU.IPR[0x80].BIT.IPR = 3;                                           */
/*                                                                              */
/*  Usage : #pragma interrupt Function_Identifier(vect=**)                      */
/*     The number of vector is "(interrupt source, name)".                      */
/*     for example :                                                            */
/*       #pragma interrupt INT_IRQ0(vect=VECT(ICU,IRQ0))          expands to :  */
/*         #pragma interrupt INT_IRQ0(vect=64)                                  */
/*       #pragma interrupt INT_CMT0_CMI0(vect=VECT(CMT0,CMI0))    expands to :  */
/*         #pragma interrupt INT_CMT0_CMI0(vect=28)                             */
/*       #pragma interrupt INT_TPU0_TGI0A(vect=VECT(TPU0,TGI0A))  expands to :  */
/*         #pragma interrupt INT_TPU0_TGI0A(vect=104)                           */
/*                                                                              */
/*  Usage : MSTPCRA,MSTPCRB,MSTPCRC of SYSTEM Register                          */
/*     The bit access operation is "MSTP(name)".                                */
/*     The name that can be used is a macro name defined with "iodefine.h".     */
/*     for example :                                                            */
/*       MSTP(TMR2) = 0;    // TMR2,TMR3,TMR23                    expands to :  */
/*         SYSTEM.MSTPCRA.BIT.MSTPA4  = 0;                                      */
/*       MSTP(SCI0) = 0;    // SCI0,SMCI0                         expands to :  */
/*         SYSTEM.MSTPCRB.BIT.MSTPB31 = 0;                                      */
/*       MSTP(TPU4) = 0;    // TPUA,TPU0,TPU1,TPU2,TPU3,TPU4,TPU5 expands to :  */
/*         SYSTEM.MSTPCRA.BIT.MSTPA13 = 0;                                      */
/*       MSTP(CMT3) = 0;    // CMT2,CMT3                          expands to :  */
/*         SYSTEM.MSTPCRA.BIT.MSTPA14 = 0;                                      */
/*                                                                              */
/*                                                                              */
/********************************************************************************/
#ifndef __RX610IODEFINE_HEADER__
#define __RX610IODEFINE_HEADER__
#pragma bit_order left
#pragma unpack
struct st_ad {
	unsigned short ADDRA;
	unsigned short ADDRB;
	unsigned short ADDRC;
	unsigned short ADDRD;
	char           wk0[8];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ADIE:1;
			unsigned char ADST:1;
			unsigned char :1;
			unsigned char CH:4;
		} BIT;
	} ADCSR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char TRGS:3;
			unsigned char :1;
			unsigned char CKS:2;
			unsigned char MODE:2;
		} BIT;
	} ADCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char DPSEL:1;
		} BIT;
	} ADDPR;
	unsigned char  ADSSTR;
};

struct st_bsc {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char STSCLR:1;
		} BIT;
	} BERCLR;
	char           wk0[3];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char TOEN:1;
			unsigned char IGAEN:1;
		} BIT;
	} BEREN;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char CPEN:1;
		} BIT;
	} BERIE;
	char           wk2[7419];
	union {
		unsigned short WORD;
		struct {
			unsigned short PRMOD:1;
			unsigned short :5;
			unsigned short PWENB:1;
			unsigned short PRENB:1;
			unsigned short :4;
			unsigned short EWENB:1;
			unsigned short :2;
			unsigned short WRMOD:1;
		} BIT;
	} CS0MOD;
	union {
		unsigned long LONG;
		struct {
			unsigned long :3;
			unsigned long CSRWAIT:5;
			unsigned long :3;
			unsigned long CSWWAIT:5;
			unsigned long :5;
			unsigned long CSPRWAIT:3;
			unsigned long :5;
			unsigned long CSPWWAIT:3;
		} BIT;
	} CS0WCNT1;
	union {
		unsigned long LONG;
		struct {
			unsigned long :1;
			unsigned long CSON:3;
			unsigned long :1;
			unsigned long WDON:3;
			unsigned long :1;
			unsigned long WRON:3;
			unsigned long :1;
			unsigned long RDON:3;
			unsigned long :5;
			unsigned long WDOFF:3;
			unsigned long :1;
			unsigned long CSWOFF:3;
			unsigned long :1;
			unsigned long CSROFF:3;
		} BIT;
	} CS0WCNT2;
	char           wk3[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short PRMOD:1;
			unsigned short :5;
			unsigned short PWENB:1;
			unsigned short PRENB:1;
			unsigned short :4;
			unsigned short EWENB:1;
			unsigned short :2;
			unsigned short WRMOD:1;
		} BIT;
	} CS1MOD;
	union {
		unsigned long LONG;
		struct {
			unsigned long :3;
			unsigned long CSRWAIT:5;
			unsigned long :3;
			unsigned long CSWWAIT:5;
			unsigned long :5;
			unsigned long CSPRWAIT:3;
			unsigned long :5;
			unsigned long CSPWWAIT:3;
		} BIT;
	} CS1WCNT1;
	union {
		unsigned long LONG;
		struct {
			unsigned long :1;
			unsigned long CSON:3;
			unsigned long :1;
			unsigned long WDON:3;
			unsigned long :1;
			unsigned long WRON:3;
			unsigned long :1;
			unsigned long RDON:3;
			unsigned long :5;
			unsigned long WDOFF:3;
			unsigned long :1;
			unsigned long CSWOFF:3;
			unsigned long :1;
			unsigned long CSROFF:3;
		} BIT;
	} CS1WCNT2;
	char           wk4[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short PRMOD:1;
			unsigned short :5;
			unsigned short PWENB:1;
			unsigned short PRENB:1;
			unsigned short :4;
			unsigned short EWENB:1;
			unsigned short :2;
			unsigned short WRMOD:1;
		} BIT;
	} CS2MOD;
	union {
		unsigned long LONG;
		struct {
			unsigned long :3;
			unsigned long CSRWAIT:5;
			unsigned long :3;
			unsigned long CSWWAIT:5;
			unsigned long :5;
			unsigned long CSPRWAIT:3;
			unsigned long :5;
			unsigned long CSPWWAIT:3;
		} BIT;
	} CS2WCNT1;
	union {
		unsigned long LONG;
		struct {
			unsigned long :1;
			unsigned long CSON:3;
			unsigned long :1;
			unsigned long WDON:3;
			unsigned long :1;
			unsigned long WRON:3;
			unsigned long :1;
			unsigned long RDON:3;
			unsigned long :5;
			unsigned long WDOFF:3;
			unsigned long :1;
			unsigned long CSWOFF:3;
			unsigned long :1;
			unsigned long CSROFF:3;
		} BIT;
	} CS2WCNT2;
	char           wk5[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short PRMOD:1;
			unsigned short :5;
			unsigned short PWENB:1;
			unsigned short PRENB:1;
			unsigned short :4;
			unsigned short EWENB:1;
			unsigned short :2;
			unsigned short WRMOD:1;
		} BIT;
	} CS3MOD;
	union {
		unsigned long LONG;
		struct {
			unsigned long :3;
			unsigned long CSRWAIT:5;
			unsigned long :3;
			unsigned long CSWWAIT:5;
			unsigned long :5;
			unsigned long CSPRWAIT:3;
			unsigned long :5;
			unsigned long CSPWWAIT:3;
		} BIT;
	} CS3WCNT1;
	union {
		unsigned long LONG;
		struct {
			unsigned long :1;
			unsigned long CSON:3;
			unsigned long :1;
			unsigned long WDON:3;
			unsigned long :1;
			unsigned long WRON:3;
			unsigned long :1;
			unsigned long RDON:3;
			unsigned long :5;
			unsigned long WDOFF:3;
			unsigned long :1;
			unsigned long CSWOFF:3;
			unsigned long :1;
			unsigned long CSROFF:3;
		} BIT;
	} CS3WCNT2;
	char           wk6[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short PRMOD:1;
			unsigned short :5;
			unsigned short PWENB:1;
			unsigned short PRENB:1;
			unsigned short :4;
			unsigned short EWENB:1;
			unsigned short :2;
			unsigned short WRMOD:1;
		} BIT;
	} CS4MOD;
	union {
		unsigned long LONG;
		struct {
			unsigned long :3;
			unsigned long CSRWAIT:5;
			unsigned long :3;
			unsigned long CSWWAIT:5;
			unsigned long :5;
			unsigned long CSPRWAIT:3;
			unsigned long :5;
			unsigned long CSPWWAIT:3;
		} BIT;
	} CS4WCNT1;
	union {
		unsigned long LONG;
		struct {
			unsigned long :1;
			unsigned long CSON:3;
			unsigned long :1;
			unsigned long WDON:3;
			unsigned long :1;
			unsigned long WRON:3;
			unsigned long :1;
			unsigned long RDON:3;
			unsigned long :5;
			unsigned long WDOFF:3;
			unsigned long :1;
			unsigned long CSWOFF:3;
			unsigned long :1;
			unsigned long CSROFF:3;
		} BIT;
	} CS4WCNT2;
	char           wk7[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short PRMOD:1;
			unsigned short :5;
			unsigned short PWENB:1;
			unsigned short PRENB:1;
			unsigned short :4;
			unsigned short EWENB:1;
			unsigned short :2;
			unsigned short WRMOD:1;
		} BIT;
	} CS5MOD;
	union {
		unsigned long LONG;
		struct {
			unsigned long :3;
			unsigned long CSRWAIT:5;
			unsigned long :3;
			unsigned long CSWWAIT:5;
			unsigned long :5;
			unsigned long CSPRWAIT:3;
			unsigned long :5;
			unsigned long CSPWWAIT:3;
		} BIT;
	} CS5WCNT1;
	union {
		unsigned long LONG;
		struct {
			unsigned long :1;
			unsigned long CSON:3;
			unsigned long :1;
			unsigned long WDON:3;
			unsigned long :1;
			unsigned long WRON:3;
			unsigned long :1;
			unsigned long RDON:3;
			unsigned long :5;
			unsigned long WDOFF:3;
			unsigned long :1;
			unsigned long CSWOFF:3;
			unsigned long :1;
			unsigned long CSROFF:3;
		} BIT;
	} CS5WCNT2;
	char           wk8[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short PRMOD:1;
			unsigned short :5;
			unsigned short PWENB:1;
			unsigned short PRENB:1;
			unsigned short :4;
			unsigned short EWENB:1;
			unsigned short :2;
			unsigned short WRMOD:1;
		} BIT;
	} CS6MOD;
	union {
		unsigned long LONG;
		struct {
			unsigned long :3;
			unsigned long CSRWAIT:5;
			unsigned long :3;
			unsigned long CSWWAIT:5;
			unsigned long :5;
			unsigned long CSPRWAIT:3;
			unsigned long :5;
			unsigned long CSPWWAIT:3;
		} BIT;
	} CS6WCNT1;
	union {
		unsigned long LONG;
		struct {
			unsigned long :1;
			unsigned long CSON:3;
			unsigned long :1;
			unsigned long WDON:3;
			unsigned long :1;
			unsigned long WRON:3;
			unsigned long :1;
			unsigned long RDON:3;
			unsigned long :5;
			unsigned long WDOFF:3;
			unsigned long :1;
			unsigned long CSWOFF:3;
			unsigned long :1;
			unsigned long CSROFF:3;
		} BIT;
	} CS6WCNT2;
	char           wk9[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short PRMOD:1;
			unsigned short :5;
			unsigned short PWENB:1;
			unsigned short PRENB:1;
			unsigned short :4;
			unsigned short EWENB:1;
			unsigned short :2;
			unsigned short WRMOD:1;
		} BIT;
	} CS7MOD;
	union {
		unsigned long LONG;
		struct {
			unsigned long :3;
			unsigned long CSRWAIT:5;
			unsigned long :3;
			unsigned long CSWWAIT:5;
			unsigned long :5;
			unsigned long CSPRWAIT:3;
			unsigned long :5;
			unsigned long CSPWWAIT:3;
		} BIT;
	} CS7WCNT1;
	union {
		unsigned long LONG;
		struct {
			unsigned long :1;
			unsigned long CSON:3;
			unsigned long :1;
			unsigned long WDON:3;
			unsigned long :1;
			unsigned long WRON:3;
			unsigned long :1;
			unsigned long RDON:3;
			unsigned long :5;
			unsigned long WDOFF:3;
			unsigned long :1;
			unsigned long CSWOFF:3;
			unsigned long :1;
			unsigned long CSROFF:3;
		} BIT;
	} CS7WCNT2;
	char           wk10[1926];
	union {
		unsigned short WORD;
		struct {
			unsigned short :7;
			unsigned short EMODE:1;
			unsigned short :2;
			unsigned short BSIZE:2;
			unsigned short :3;
			unsigned short EXENB:1;
		} BIT;
	} CS0CNT;
	char           wk11[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS0REC;
	char           wk12[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :7;
			unsigned short EMODE:1;
			unsigned short :2;
			unsigned short BSIZE:2;
			unsigned short :3;
			unsigned short EXENB:1;
		} BIT;
	} CS1CNT;
	char           wk13[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS1REC;
	char           wk14[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :7;
			unsigned short EMODE:1;
			unsigned short :2;
			unsigned short BSIZE:2;
			unsigned short :3;
			unsigned short EXENB:1;
		} BIT;
	} CS2CNT;
	char           wk15[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS2REC;
	char           wk16[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :7;
			unsigned short EMODE:1;
			unsigned short :2;
			unsigned short BSIZE:2;
			unsigned short :3;
			unsigned short EXENB:1;
		} BIT;
	} CS3CNT;
	char           wk17[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS3REC;
	char           wk18[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :7;
			unsigned short EMODE:1;
			unsigned short :2;
			unsigned short BSIZE:2;
			unsigned short :3;
			unsigned short EXENB:1;
		} BIT;
	} CS4CNT;
	char           wk19[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS4REC;
	char           wk20[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :7;
			unsigned short EMODE:1;
			unsigned short :2;
			unsigned short BSIZE:2;
			unsigned short :3;
			unsigned short EXENB:1;
		} BIT;
	} CS5CNT;
	char           wk21[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS5REC;
	char           wk22[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :7;
			unsigned short EMODE:1;
			unsigned short :2;
			unsigned short BSIZE:2;
			unsigned short :3;
			unsigned short EXENB:1;
		} BIT;
	} CS6CNT;
	char           wk23[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS6REC;
	char           wk24[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :7;
			unsigned short EMODE:1;
			unsigned short :2;
			unsigned short BSIZE:2;
			unsigned short :3;
			unsigned short EXENB:1;
		} BIT;
	} CS7CNT;
	char           wk25[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS7REC;
};

struct st_cmt {
	union {
		unsigned short WORD;
		struct {
			unsigned short :14;
			unsigned short STR1:1;
			unsigned short STR0:1;
		} BIT;
	} CMSTR0;
	char           wk0[14];
	union {
		unsigned short WORD;
		struct {
			unsigned short :14;
			unsigned short STR3:1;
			unsigned short STR2:1;
		} BIT;
	} CMSTR1;
};

struct st_cmt0 {
	union {
		unsigned short WORD;
		struct {
			unsigned short :9;
			unsigned short CMIE:1;
			unsigned short :4;
			unsigned short CKS:2;
		} BIT;
	} CMCR;
	unsigned short CMCNT;
	unsigned short CMCOR;
};

struct st_crc {
	union {
		unsigned char BYTE;
		struct {
			unsigned char DORCLR:1;
			unsigned char :4;
			unsigned char LMS:1;
			unsigned char GPS:2;
		} BIT;
	} CRCCR;
	unsigned char  CRCDIR;
	unsigned short CRCDOR;
};

struct st_da {
	unsigned short DADR0;
	unsigned short DADR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char DAOE1:1;
			unsigned char DAOE0:1;
			unsigned char DAE:1;
		} BIT;
	} DACR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char DPSEL:1;
		} BIT;
	} DADPR;
};

struct st_dmac {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DMST:1;
		} BIT;
	} DMSCNT;
	char           wk0[8];
	union {
		unsigned char BYTE;
		struct {
			unsigned char DINTM0:1;
			unsigned char DINTM1:1;
			unsigned char DINTM2:1;
			unsigned char DINTM3:1;
		} BIT;
	} DMICNT;
	char           wk1[11];
	union {
		unsigned char BYTE;
		struct {
			unsigned char DEDET0:1;
			unsigned char DEDET1:1;
			unsigned char DEDET2:1;
			unsigned char DEDET3:1;
		} BIT;
	} DMEDET;
	char           wk2[3];
	union {
		unsigned char BYTE;
		struct {
			unsigned char DASTS0:1;
			unsigned char DASTS1:1;
			unsigned char DASTS2:1;
			unsigned char DASTS3:1;
		} BIT;
	} DMASTS;
};

struct st_dmac0 {
	void          *DMCSA;
	void          *DMCDA;
	unsigned long  DMCBC;
	union {
		unsigned long LONG;
		struct {
			unsigned long :4;
			unsigned long OPSEL:4;
			unsigned long :5;
			unsigned long SZSEL:3;
			unsigned long :1;
			unsigned long SMOD:3;
			unsigned long :1;
			unsigned long DMOD:3;
		} BIT;
	} DMMOD;
	char           wk0[496];
	void          *DMRSA;
	void          *DMRDA;
	unsigned long  DMRBC;
	char           wk1[500];
	union {
		unsigned long LONG;
		struct {
			unsigned long :6;
			unsigned long DSEL:2;
			unsigned long :13;
			unsigned long BRLOD:1;
			unsigned long SRLOD:1;
			unsigned long DRLOD:1;
			unsigned long :2;
			unsigned long DCTG:6;
		} BIT;
	} DMCRA;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DSCLR:1;
		} BIT;
	} DMCRB;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char ECLR:1;
		} BIT;
	} DMCRC;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DREQ:1;
		} BIT;
	} DMCRD;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DEN:1;
		} BIT;
	} DMCRE;
};

struct st_dmac1 {
	void          *DMCSA;
	void          *DMCDA;
	unsigned long  DMCBC;
	union {
		unsigned long LONG;
		struct {
			unsigned long :4;
			unsigned long OPSEL:4;
			unsigned long :5;
			unsigned long SZSEL:3;
			unsigned long :1;
			unsigned long SMOD:3;
			unsigned long :1;
			unsigned long DMOD:3;
		} BIT;
	} DMMOD;
	char           wk0[496];
	void          *DMRSA;
	void          *DMRDA;
	unsigned long  DMRBC;
	char           wk1[492];
	union {
		unsigned long LONG;
		struct {
			unsigned long :6;
			unsigned long DSEL:2;
			unsigned long :13;
			unsigned long BRLOD:1;
			unsigned long SRLOD:1;
			unsigned long DRLOD:1;
			unsigned long :2;
			unsigned long DCTG:6;
		} BIT;
	} DMCRA;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DSCLR:1;
		} BIT;
	} DMCRB;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char ECLR:1;
		} BIT;
	} DMCRC;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DREQ:1;
		} BIT;
	} DMCRD;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DEN:1;
		} BIT;
	} DMCRE;
};

struct st_dmac2 {
	void          *DMCSA;
	void          *DMCDA;
	unsigned long  DMCBC;
	union {
		unsigned long LONG;
		struct {
			unsigned long :4;
			unsigned long OPSEL:4;
			unsigned long :5;
			unsigned long SZSEL:3;
			unsigned long :1;
			unsigned long SMOD:3;
			unsigned long :1;
			unsigned long DMOD:3;
		} BIT;
	} DMMOD;
	char           wk0[496];
	void          *DMRSA;
	void          *DMRDA;
	unsigned long  DMRBC;
	char           wk1[484];
	union {
		unsigned long LONG;
		struct {
			unsigned long :6;
			unsigned long DSEL:2;
			unsigned long :13;
			unsigned long BRLOD:1;
			unsigned long SRLOD:1;
			unsigned long DRLOD:1;
			unsigned long :2;
			unsigned long DCTG:6;
		} BIT;
	} DMCRA;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DSCLR:1;
		} BIT;
	} DMCRB;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char ECLR:1;
		} BIT;
	} DMCRC;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DREQ:1;
		} BIT;
	} DMCRD;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DEN:1;
		} BIT;
	} DMCRE;
};

struct st_dmac3 {
	void          *DMCSA;
	void          *DMCDA;
	unsigned long  DMCBC;
	union {
		unsigned long LONG;
		struct {
			unsigned long :4;
			unsigned long OPSEL:4;
			unsigned long :5;
			unsigned long SZSEL:3;
			unsigned long :1;
			unsigned long SMOD:3;
			unsigned long :1;
			unsigned long DMOD:3;
		} BIT;
	} DMMOD;
	char           wk0[496];
	void          *DMRSA;
	void          *DMRDA;
	unsigned long  DMRBC;
	char           wk1[476];
	union {
		unsigned long LONG;
		struct {
			unsigned long :6;
			unsigned long DSEL:2;
			unsigned long :13;
			unsigned long BRLOD:1;
			unsigned long SRLOD:1;
			unsigned long DRLOD:1;
			unsigned long :2;
			unsigned long DCTG:6;
		} BIT;
	} DMCRA;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DSCLR:1;
		} BIT;
	} DMCRB;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char ECLR:1;
		} BIT;
	} DMCRC;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DREQ:1;
		} BIT;
	} DMCRD;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DEN:1;
		} BIT;
	} DMCRE;
};

struct st_dtc {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char RRS:1;
			unsigned char RCHNE:1;
			unsigned char :2;
			unsigned char ERR:1;
		} BIT;
	} DTCCR;
	char           wk0[3];
	void          *DTCVBR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char SHORT:1;
		} BIT;
	} DTCADMOD;
	char           wk1[3];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DTCST:1;
		} BIT;
	} DTCST;
};

struct st_flash {
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char FLWE:2;
		} BIT;
	} FWEPROR;
	char           wk1[7799160];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char FRDMD:1;
		} BIT;
	} FMODR;
	char           wk2[13];
	union {
		unsigned char BYTE;
		struct {
			unsigned char ROMAE:1;
			unsigned char :2;
			unsigned char CMDLK:1;
			unsigned char DFLAE:1;
			unsigned char :1;
			unsigned char DFLRPE:1;
			unsigned char DFLWPE:1;
		} BIT;
	} FASTAT;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ROMAEIE:1;
			unsigned char :2;
			unsigned char CMDLKIE:1;
			unsigned char DFLAEIE:1;
			unsigned char :1;
			unsigned char DFLRPEIE:1;
			unsigned char DFLWPEIE:1;
		} BIT;
	} FAEINT;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char FRDYIE:1;
		} BIT;
	} FRDYIE;
	char           wk3[45];
	union {
		unsigned short WORD;
		struct {
			unsigned short KEY:8;
			unsigned short :4;
			unsigned short DBRE3:1;
			unsigned short DBRE2:1;
			unsigned short DBRE1:1;
			unsigned short DBRE0:1;
		} BIT;
	} DFLRE;
	char           wk4[14];
	union {
		unsigned short WORD;
		struct {
			unsigned short KEY:8;
			unsigned short :4;
			unsigned short DBWE3:1;
			unsigned short DBWE2:1;
			unsigned short DBWE1:1;
			unsigned short DBWE0:1;
		} BIT;
	} DFLWE;
	char           wk5[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short KEY:8;
			unsigned short :7;
			unsigned short FCRME:1;
		} BIT;
	} FCURAME;
	char           wk6[15194];
	union {
		unsigned char BYTE;
		struct {
			unsigned char FRDY:1;
			unsigned char ILGLERR:1;
			unsigned char ERSERR:1;
			unsigned char PRGERR:1;
			unsigned char SUSRDY:1;
			unsigned char :1;
			unsigned char ERSSPD:1;
			unsigned char PRGSPD:1;
		} BIT;
	} FSTATR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char FCUERR:1;
			unsigned char :2;
			unsigned char FLOCKST:1;
		} BIT;
	} FSTATR1;
	union {
		unsigned short WORD;
		struct {
			unsigned short FEKEY:8;
			unsigned short FENTRYD:1;
			unsigned short :5;
			unsigned short FENTRY1:1;
			unsigned short FENTRY0:1;
		} BIT;
	} FENTRYR;
	union {
		unsigned short WORD;
		struct {
			unsigned short FPKEY:8;
			unsigned short :7;
			unsigned short FPROTCN:1;
		} BIT;
	} FPROTR;
	union {
		unsigned short WORD;
		struct {
			unsigned short FRKEY:8;
			unsigned short :7;
			unsigned short FRESET:1;
		} BIT;
	} FRESETR;
	char           wk7[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short CMDR:8;
			unsigned short PCMDR:8;
		} BIT;
	} FCMDR;
	char           wk8[12];
	union {
		unsigned short WORD;
		struct {
			unsigned short :15;
			unsigned short ESUSPMD:1;
		} BIT;
	} FCPSR;
	union {
		unsigned short WORD;
		struct {
			unsigned short :3;
			unsigned short BCADR:10;
			unsigned short :2;
			unsigned short BCSIZE:1;
		} BIT;
	} DFLBCCNT;
	union {
		unsigned short WORD;
		struct {
			unsigned short :8;
			unsigned short PEERRST:8;
		} BIT;
	} FPESTAT;
	union {
		unsigned short WORD;
		struct {
			unsigned short :15;
			unsigned short BCST:1;
		} BIT;
	} DFLBCSTAT;
	char           wk9[24];
	union {
		unsigned short WORD;
		struct {
			unsigned short :8;
			unsigned short PCKA:8;
		} BIT;
	} PCKAR;
};

struct st_icu {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char IR:1;
		} BIT;
	} IR[255];
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char ISEL:2;
		} BIT;
	} ISELR[255];
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char IEN7:1;
			unsigned char IEN6:1;
			unsigned char IEN5:1;
			unsigned char IEN4:1;
			unsigned char IEN3:1;
			unsigned char IEN2:1;
			unsigned char IEN1:1;
			unsigned char IEN0:1;
		} BIT;
	} IER[32];
	char           wk2[224];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char IPR:3;
		} BIT;
	} IPR[144];
	char           wk3[96];
	union {
		unsigned short WORD;
		struct {
			unsigned short FIEN:1;
			unsigned short :7;
			unsigned short FVCT:8;
		} BIT;
	} FIR;
	char           wk4[20238];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char IRQEN:1;
		} BIT;
	} IRQER[16];
	char           wk5[16];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char IRQMD:2;
		} BIT;
	} IRQCR[16];
	char           wk6[16];
	union {
		unsigned short WORD;
		struct {
			unsigned short SSI15:1;
			unsigned short SSI14:1;
			unsigned short SSI13:1;
			unsigned short SSI12:1;
			unsigned short SSI11:1;
			unsigned short SSI10:1;
			unsigned short SSI9:1;
			unsigned short SSI8:1;
			unsigned short SSI7:1;
			unsigned short SSI6:1;
			unsigned short SSI5:1;
			unsigned short SSI4:1;
			unsigned short SSI3:1;
			unsigned short SSI2:1;
			unsigned short SSI1:1;
			unsigned short SSI0:1;
		} BIT;
	} SSIER;
	char           wk7[14];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char NMIEN:1;
		} BIT;
	} NMIER;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char NMIMD:1;
		} BIT;
	} NMICR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char NMIST:1;
		} BIT;
	} NMISR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char NMICLR:1;
		} BIT;
	} NMICLR;
};

struct st_ioport {
	union {
		unsigned char BYTE;
		struct {
			unsigned char CS7E:1;
			unsigned char CS6E:1;
			unsigned char CS5E:1;
			unsigned char CS4E:1;
			unsigned char CS3E:1;
			unsigned char CS2E:1;
			unsigned char CS1E:1;
			unsigned char CS0E:1;
		} BIT;
	} PFCR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char CS7S:2;
			unsigned char CS6S:2;
			unsigned char CS5S:2;
			unsigned char CS4S:2;
		} BIT;
	} PFCR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char CS3S:1;
			unsigned char CS2S:1;
		} BIT;
	} PFCR2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char A23E:1;
			unsigned char A22E:1;
			unsigned char A21E:1;
			unsigned char A20E:1;
			unsigned char A19E:1;
			unsigned char A18E:1;
			unsigned char A17E:1;
			unsigned char A16E:1;
		} BIT;
	} PFCR3;
	union {
		unsigned char BYTE;
		struct {
			unsigned char A15E:1;
			unsigned char A14E:1;
			unsigned char A13E:1;
			unsigned char A12E:1;
			unsigned char A11E:1;
			unsigned char A10E:1;
			unsigned char A9E:1;
			unsigned char A8E:1;
		} BIT;
	} PFCR4;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char WR1BC1E:1;
			unsigned char :1;
			unsigned char DHE:1;
			unsigned char TCLKS:1;
		} BIT;
	} PFCR5;
	union {
		unsigned char BYTE;
		struct {
			unsigned char TPUMS5:1;
			unsigned char TPUMS4:1;
			unsigned char TPUMS3A:1;
			unsigned char TPUMS3B:1;
			unsigned char TPUMS2:1;
			unsigned char TPUMS1:1;
			unsigned char TPUMS0A:1;
			unsigned char TPUMS0B:1;
		} BIT;
	} PFCR6;
	union {
		unsigned char BYTE;
		struct {
			unsigned char TPUMS11:1;
			unsigned char TPUMS10:1;
			unsigned char TPUMS9A:1;
			unsigned char TPUMS9B:1;
			unsigned char TPUMS8:1;
			unsigned char TPUMS7:1;
			unsigned char TPUMS6A:1;
			unsigned char TPUMS6B:1;
		} BIT;
	} PFCR7;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ITS15:1;
			unsigned char ITS14:1;
			unsigned char ITS13:1;
			unsigned char ITS12:1;
			unsigned char ITS11:1;
			unsigned char ITS10:1;
			unsigned char ITS9:1;
			unsigned char ITS8:1;
		} BIT;
	} PFCR8;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ITS7:1;
			unsigned char ITS6:1;
			unsigned char ITS5:1;
			unsigned char ITS4:1;
			unsigned char ITS3:1;
			unsigned char ITS2:1;
			unsigned char ITS1:1;
			unsigned char ITS0:1;
		} BIT;
	} PFCR9;
};

struct st_port0 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PORT;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ICR;
};

struct st_port1 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PORT;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ICR;
};

struct st_port2 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PORT;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ICR;
	char           wk3[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ODR;
};

struct st_port3 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PORT;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ICR;
};

struct st_port4 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PORT;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ICR;
};

struct st_port5 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PORT;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ICR;
};

struct st_port6 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PORT;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ICR;
};

struct st_port7 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PORT;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ICR;
};

struct st_port8 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PORT;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ICR;
};

struct st_port9 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PORT;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ICR;
};

struct st_porta {
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PORT;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ICR;
	char           wk3[95];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PCR;
};

struct st_portb {
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PORT;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ICR;
	char           wk3[95];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PCR;
};

struct st_portc {
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PORT;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ICR;
	char           wk3[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ODR;
	char           wk4[63];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PCR;
};

struct st_portd {
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PORT;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ICR;
	char           wk3[95];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PCR;
};

struct st_porte {
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PORT;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ICR;
	char           wk3[95];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PCR;
};

struct st_portf {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PORT;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ICR;
};

struct st_portg {
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PORT;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ICR;
};

struct st_porth {
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PORT;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ICR;
};

struct st_ppg0 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char G3CMS:2;
			unsigned char G2CMS:2;
			unsigned char G1CMS:2;
			unsigned char G0CMS:2;
		} BIT;
	} PCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char G3INV:1;
			unsigned char G2INV:1;
			unsigned char G1INV:1;
			unsigned char G0INV:1;
			unsigned char G3NOV:1;
			unsigned char G2NOV:1;
			unsigned char G1NOV:1;
			unsigned char G0NOV:1;
		} BIT;
	} PMR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char NDER15:1;
			unsigned char NDER14:1;
			unsigned char NDER13:1;
			unsigned char NDER12:1;
			unsigned char NDER11:1;
			unsigned char NDER10:1;
			unsigned char NDER9:1;
			unsigned char NDER8:1;
		} BIT;
	} NDERH;
	union {
		unsigned char BYTE;
		struct {
			unsigned char NDER7:1;
			unsigned char NDER6:1;
			unsigned char NDER5:1;
			unsigned char NDER4:1;
			unsigned char NDER3:1;
			unsigned char NDER2:1;
			unsigned char NDER1:1;
			unsigned char NDER0:1;
		} BIT;
	} NDERL;
	union {
		unsigned char BYTE;
		struct {
			unsigned char POD15:1;
			unsigned char POD14:1;
			unsigned char POD13:1;
			unsigned char POD12:1;
			unsigned char POD11:1;
			unsigned char POD10:1;
			unsigned char POD9:1;
			unsigned char POD8:1;
		} BIT;
	} PODRH;
	union {
		unsigned char BYTE;
		struct {
			unsigned char POD7:1;
			unsigned char POD6:1;
			unsigned char POD5:1;
			unsigned char POD4:1;
			unsigned char POD3:1;
			unsigned char POD2:1;
			unsigned char POD1:1;
			unsigned char POD0:1;
		} BIT;
	} PODRL;
	union {
		unsigned char BYTE;
		struct {
			unsigned char NDR15:1;
			unsigned char NDR14:1;
			unsigned char NDR13:1;
			unsigned char NDR12:1;
			unsigned char NDR11:1;
			unsigned char NDR10:1;
			unsigned char NDR9:1;
			unsigned char NDR8:1;
		} BIT;
	} NDRH;
	union {
		unsigned char BYTE;
		struct {
			unsigned char NDR7:1;
			unsigned char NDR6:1;
			unsigned char NDR5:1;
			unsigned char NDR4:1;
			unsigned char NDR3:1;
			unsigned char NDR2:1;
			unsigned char NDR1:1;
			unsigned char NDR0:1;
		} BIT;
	} NDRL;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char NDR11:1;
			unsigned char NDR10:1;
			unsigned char NDR9:1;
			unsigned char NDR8:1;
		} BIT;
	} NDRH2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char NDR3:1;
			unsigned char NDR2:1;
			unsigned char NDR1:1;
			unsigned char NDR0:1;
		} BIT;
	} NDRL2;
};

struct st_ppg1 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char PTRSL:1;
		} BIT;
	} PTRSLR;
	char           wk0[5];
	union {
		unsigned char BYTE;
		struct {
			unsigned char G3CMS:2;
			unsigned char G2CMS:2;
			unsigned char G1CMS:2;
			unsigned char G0CMS:2;
		} BIT;
	} PCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char G3INV:1;
			unsigned char G2INV:1;
			unsigned char G1INV:1;
			unsigned char G0INV:1;
			unsigned char G3NOV:1;
			unsigned char G2NOV:1;
			unsigned char G1NOV:1;
			unsigned char G0NOV:1;
		} BIT;
	} PMR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char NDER31:1;
			unsigned char NDER30:1;
			unsigned char NDER29:1;
			unsigned char NDER28:1;
			unsigned char NDER27:1;
			unsigned char NDER26:1;
			unsigned char NDER25:1;
			unsigned char NDER24:1;
		} BIT;
	} NDERH;
	union {
		unsigned char BYTE;
		struct {
			unsigned char NDER23:1;
			unsigned char NDER22:1;
			unsigned char NDER21:1;
			unsigned char NDER20:1;
			unsigned char NDER19:1;
			unsigned char NDER18:1;
			unsigned char NDER17:1;
			unsigned char NDER16:1;
		} BIT;
	} NDERL;
	union {
		unsigned char BYTE;
		struct {
			unsigned char POD31:1;
			unsigned char POD30:1;
			unsigned char POD29:1;
			unsigned char POD28:1;
			unsigned char POD27:1;
			unsigned char POD26:1;
			unsigned char POD25:1;
			unsigned char POD24:1;
		} BIT;
	} PODRH;
	union {
		unsigned char BYTE;
		struct {
			unsigned char POD23:1;
			unsigned char POD22:1;
			unsigned char POD21:1;
			unsigned char POD20:1;
			unsigned char POD19:1;
			unsigned char POD18:1;
			unsigned char POD17:1;
			unsigned char POD16:1;
		} BIT;
	} PODRL;
	union {
		unsigned char BYTE;
		struct {
			unsigned char NDR31:1;
			unsigned char NDR30:1;
			unsigned char NDR29:1;
			unsigned char NDR28:1;
			unsigned char NDR27:1;
			unsigned char NDR26:1;
			unsigned char NDR25:1;
			unsigned char NDR24:1;
		} BIT;
	} NDRH;
	union {
		unsigned char BYTE;
		struct {
			unsigned char NDR23:1;
			unsigned char NDR22:1;
			unsigned char NDR21:1;
			unsigned char NDR20:1;
			unsigned char NDR19:1;
			unsigned char NDR18:1;
			unsigned char NDR17:1;
			unsigned char NDR16:1;
		} BIT;
	} NDRL;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char NDR27:1;
			unsigned char NDR26:1;
			unsigned char NDR25:1;
			unsigned char NDR24:1;
		} BIT;
	} NDRH2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char NDR19:1;
			unsigned char NDR18:1;
			unsigned char NDR17:1;
			unsigned char NDR16:1;
		} BIT;
	} NDRL2;
};

struct st_riic {
	union {
		unsigned char BYTE;
		struct {
			unsigned char ICE:1;
			unsigned char IICRST:1;
			unsigned char CLO:1;
			unsigned char SOWP:1;
			unsigned char SCLO:1;
			unsigned char SDAO:1;
			unsigned char SCLI:1;
			unsigned char SDAI:1;
		} BIT;
	} ICCR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char BBSY:1;
			unsigned char MST:1;
			unsigned char TRS:1;
			unsigned char :1;
			unsigned char SP:1;
			unsigned char RS:1;
			unsigned char ST:1;
		} BIT;
	} ICCR2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char MTWP:1;
			unsigned char CKS:3;
			unsigned char BCWP:1;
			unsigned char BC:3;
		} BIT;
	} ICMR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char DLCS:1;
			unsigned char SDDL:3;
			unsigned char :1;
			unsigned char TMOH:1;
			unsigned char TMOL:1;
			unsigned char TMOS:1;
		} BIT;
	} ICMR2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SMBS:1;
			unsigned char WAIT:1;
			unsigned char RDRFS:1;
			unsigned char ACKWP:1;
			unsigned char ACKBT:1;
			unsigned char ACKBR:1;
			unsigned char NF:2;
		} BIT;
	} ICMR3;
	union {
		unsigned char BYTE;
		struct {
			unsigned char FMPE:1;
			unsigned char SCLE:1;
			unsigned char NFE:1;
			unsigned char NACKE:1;
			unsigned char SALE:1;
			unsigned char NALE:1;
			unsigned char MALE:1;
			unsigned char TMOE:1;
		} BIT;
	} ICFER;
	union {
		unsigned char BYTE;
		struct {
			unsigned char HOAE:1;
			unsigned char :1;
			unsigned char DIDE:1;
			unsigned char :1;
			unsigned char GCAE:1;
			unsigned char SAR2E:1;
			unsigned char SAR1E:1;
			unsigned char SAR0E:1;
		} BIT;
	} ICSER;
	union {
		unsigned char BYTE;
		struct {
			unsigned char TIE:1;
			unsigned char TEIE:1;
			unsigned char RIE:1;
			unsigned char NAKIE:1;
			unsigned char SPIE:1;
			unsigned char STIE:1;
			unsigned char ALIE:1;
			unsigned char TMOIE:1;
		} BIT;
	} ICIER;
	union {
		unsigned char BYTE;
		struct {
			unsigned char HOA:1;
			unsigned char :1;
			unsigned char DID:1;
			unsigned char :1;
			unsigned char GCA:1;
			unsigned char AAS2:1;
			unsigned char AAS1:1;
			unsigned char AAS0:1;
		} BIT;
	} ICSR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char TDRE:1;
			unsigned char TEND:1;
			unsigned char RDRF:1;
			unsigned char NACKF:1;
			unsigned char STOP:1;
			unsigned char START:1;
			unsigned char AL:1;
			unsigned char TMOF:1;
		} BIT;
	} ICSR2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SVA:7;
			unsigned char SVA0:1;
		} BIT;
	} SARL0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char SVA:2;
			unsigned char FS:1;
		} BIT;
	} SARU0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SVA:7;
			unsigned char SVA0:1;
		} BIT;
	} SARL1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char SVA:2;
			unsigned char FS:1;
		} BIT;
	} SARU1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SVA:7;
			unsigned char SVA0:1;
		} BIT;
	} SARL2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char SVA:2;
			unsigned char FS:1;
		} BIT;
	} SARU2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char BRL:5;
		} BIT;
	} ICBRL;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char BRH:5;
		} BIT;
	} ICBRH;
	unsigned char  ICDRT;
	unsigned char  ICDRR;
};

struct st_sci {
	union {
		unsigned char BYTE;
		struct {
			unsigned char CM:1;
			unsigned char CHR:1;
			unsigned char PE:1;
			unsigned char PM:1;
			unsigned char STOP:1;
			unsigned char :1;
			unsigned char CKS:2;
		} BIT;
	} SMR;
	unsigned char  BRR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char TIE:1;
			unsigned char RIE:1;
			unsigned char TE:1;
			unsigned char RE:1;
			unsigned char :1;
			unsigned char TEIE:1;
			unsigned char CKE:2;
		} BIT;
	} SCR;
	unsigned char  TDR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char TDRE:1;
			unsigned char RDRF:1;
			unsigned char ORER:1;
			unsigned char FER:1;
			unsigned char PER:1;
			unsigned char TEND:1;
		} BIT;
	} SSR;
	unsigned char  RDR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char SDIR:1;
			unsigned char SINV:1;
			unsigned char :1;
			unsigned char SMIF:1;
		} BIT;
	} SCMR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char ABCS:1;
			unsigned char :3;
			unsigned char ACS0:1;
		} BIT;
	} SEMR;
};

struct st_smci {
	union {
		unsigned char BYTE;
		struct {
			unsigned char GM:1;
			unsigned char BLK:1;
			unsigned char PE:1;
			unsigned char PM:1;
			unsigned char BCP:2;
			unsigned char CKS:2;
		} BIT;
	} SMR;
	unsigned char  BRR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char TIE:1;
			unsigned char RIE:1;
			unsigned char TE:1;
			unsigned char RE:1;
			unsigned char :1;
			unsigned char TEIE:1;
			unsigned char CKE:2;
		} BIT;
	} SCR;
	unsigned char  TDR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char TDRE:1;
			unsigned char RDRF:1;
			unsigned char ORER:1;
			unsigned char ERS:1;
			unsigned char PER:1;
			unsigned char TEND:1;
		} BIT;
	} SSR;
	unsigned char  RDR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char BCP2:1;
			unsigned char :3;
			unsigned char SDIR:1;
			unsigned char SINV:1;
			unsigned char :1;
			unsigned char SMIF:1;
		} BIT;
	} SCMR;
};

struct st_system {
	union {
		unsigned short WORD;
		struct {
			unsigned short :8;
			unsigned short MDE:1;
			unsigned short :5;
			unsigned short MD1:1;
			unsigned short MD0:1;
		} BIT;
	} MDMONR;
	union {
		unsigned short WORD;
		struct {
			unsigned short :9;
			unsigned short UBTS:1;
			unsigned short :1;
			unsigned short BOTS:1;
			unsigned short BSW:2;
			unsigned short EXB:1;
			unsigned short IROM:1;
		} BIT;
	} MDSR;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short KEY:8;
			unsigned short :6;
			unsigned short EXBE:1;
			unsigned short ROME:1;
		} BIT;
	} SYSCR0;
	union {
		unsigned short WORD;
		struct {
			unsigned short :15;
			unsigned short RAME:1;
		} BIT;
	} SYSCR1;
	char           wk1[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short SSBY:1;
			unsigned short OPE:1;
			unsigned short :1;
			unsigned short STS:5;
		} BIT;
	} SBYCR;
	char           wk2[2];
	union {
		unsigned long LONG;
		struct {
			unsigned long ACSE:1;
			unsigned long :2;
			unsigned long MSTPA28:1;
			unsigned long MSTPA27:1;
			unsigned long :3;
			unsigned long MSTPA23:1;
			unsigned long MSTPA22:1;
			unsigned long MSTPA21:1;
			unsigned long MSTPA20:1;
			unsigned long MSTPA19:1;
			unsigned long :3;
			unsigned long MSTPA15:1;
			unsigned long MSTPA14:1;
			unsigned long MSTPA13:1;
			unsigned long MSTPA12:1;
			unsigned long MSTPA11:1;
			unsigned long MSTPA10:1;
			unsigned long :4;
			unsigned long MSTPA5:1;
			unsigned long MSTPA4:1;
		} BIT;
	} MSTPCRA;
	union {
		unsigned long LONG;
		struct {
			unsigned long MSTPB31:1;
			unsigned long MSTPB30:1;
			unsigned long MSTPB29:1;
			unsigned long MSTPB28:1;
			unsigned long MSTPB27:1;
			unsigned long MSTPB26:1;
			unsigned long MSTPB25:1;
			unsigned long :1;
			unsigned long MSTPB23:1;
			unsigned long :1;
			unsigned long MSTPB21:1;
			unsigned long MSTPB20:1;
		} BIT;
	} MSTPCRB;
	union {
		unsigned long LONG;
		struct {
			unsigned long :30;
			unsigned long MSTPC1:1;
			unsigned long MSTPC0:1;
		} BIT;
	} MSTPCRC;
	char           wk3[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :4;
			unsigned long ICK:4;
			unsigned long PSTOP1:1;
			unsigned long :3;
			unsigned long BCK:4;
			unsigned long :4;
			unsigned long PCK:4;
		} BIT;
	} SCKCR;
	char           wk4[49756];
	union {
		unsigned char BYTE;
		struct {
			unsigned char DPSBY:1;
			unsigned char IOKEEP:1;
			unsigned char RAMCUT2:1;
			unsigned char RAMCUT1:1;
			unsigned char :3;
			unsigned char RAMCUT0:1;
		} BIT;
	} DPSBYCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char WTSTS:6;
		} BIT;
	} DPSWCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char DNMIE:1;
			unsigned char :3;
			unsigned char DIRQ3E:1;
			unsigned char DIRQ2E:1;
			unsigned char DIRQ1E:1;
			unsigned char DIRQ0E:1;
		} BIT;
	} DPSIER;
	union {
		unsigned char BYTE;
		struct {
			unsigned char DNMIF:1;
			unsigned char :3;
			unsigned char DIRQ3F:1;
			unsigned char DIRQ2F:1;
			unsigned char DIRQ1F:1;
			unsigned char DIRQ0F:1;
		} BIT;
	} DPSIFR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char DNMIEG:1;
			unsigned char :3;
			unsigned char DIRQ3EG:1;
			unsigned char DIRQ2EG:1;
			unsigned char DIRQ1EG:1;
			unsigned char DIRQ0EG:1;
		} BIT;
	} DPSIEGR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char DPSRSTF:1;
		} BIT;
	} RSTSR;
	char           wk5[10];
	unsigned char  DPSBKR[32];
};

struct st_tmr0 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char CMIEB:1;
			unsigned char CMIEA:1;
			unsigned char OVIE:1;
			unsigned char CCLR:2;
		} BIT;
	} TCR;
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char ADTE:1;
			unsigned char OSB:2;
			unsigned char OSA:2;
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
			unsigned char TMRIS:1;
			unsigned char :2;
			unsigned char CSS:2;
			unsigned char CKS:3;
		} BIT;
	} TCCR;
};

struct st_tmr1 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char CMIEB:1;
			unsigned char CMIEA:1;
			unsigned char OVIE:1;
			unsigned char CCLR:2;
		} BIT;
	} TCR;
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char OSB:2;
			unsigned char OSA:2;
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
			unsigned char TMRIS:1;
			unsigned char :2;
			unsigned char CSS:2;
			unsigned char CKS:3;
		} BIT;
	} TCCR;
};

struct st_tmr01 {
	unsigned short TCORA;
	unsigned short TCORB;
	unsigned short TCNT;
	unsigned short TCCR;
};

struct st_tpu0 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char CCLR:3;
			unsigned char CKEG:2;
			unsigned char TPSC:3;
		} BIT;
	} TCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ICSELD:1;
			unsigned char ICSELB:1;
			unsigned char BFB:1;
			unsigned char BFA:1;
			unsigned char MD:4;
		} BIT;
	} TMDR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char IOB:4;
			unsigned char IOA:4;
		} BIT;
	} TIORH;
	union {
		unsigned char BYTE;
		struct {
			unsigned char IOD:4;
			unsigned char IOC:4;
		} BIT;
	} TIORL;
	union {
		unsigned char BYTE;
		struct {
			unsigned char TTGE:1;
			unsigned char :2;
			unsigned char TCIEV:1;
			unsigned char TGIED:1;
			unsigned char TGIEC:1;
			unsigned char TGIEB:1;
			unsigned char TGIEA:1;
		} BIT;
	} TIER;
	unsigned char  TSR;
	unsigned short TCNT;
	unsigned short TGRA;
	unsigned short TGRB;
	unsigned short TGRC;
	unsigned short TGRD;
};

struct st_tpu1 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char CCLR:3;
			unsigned char CKEG:2;
			unsigned char TPSC:3;
		} BIT;
	} TCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ICSELB:1;
			unsigned char :2;
			unsigned char MD:4;
		} BIT;
	} TMDR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char IOB:4;
			unsigned char IOA:4;
		} BIT;
	} TIOR;
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char TTGE:1;
			unsigned char :1;
			unsigned char TCIEU:1;
			unsigned char TCIEV:1;
			unsigned char :2;
			unsigned char TGIEB:1;
			unsigned char TGIEA:1;
		} BIT;
	} TIER;
	union {
		unsigned char BYTE;
		struct {
			unsigned char TCFD:1;
		} BIT;
	} TSR;
	unsigned short TCNT;
	unsigned short TGRA;
	unsigned short TGRB;
};

struct st_tpua {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char CST5:1;
			unsigned char CST4:1;
			unsigned char CST3:1;
			unsigned char CST2:1;
			unsigned char CST1:1;
			unsigned char CST0:1;
		} BIT;
	} TSTR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char SYNC5:1;
			unsigned char SYNC4:1;
			unsigned char SYNC3:1;
			unsigned char SYNC2:1;
			unsigned char SYNC1:1;
			unsigned char SYNC0:1;
		} BIT;
	} TSYR;
};

union un_wdt {
	struct {
		unsigned short WINA;
		unsigned short WINB;
	} WRITE;
	struct {
		union {
			unsigned char BYTE;
			struct {
				unsigned char :1;
				unsigned char TMS:1;
				unsigned char TME:1;
				unsigned char :2;
				unsigned char CKS:3;
			} BIT;
		} TCSR;
		unsigned char  TCNT;
		char           wk0[1];
		union {
			unsigned char BYTE;
			struct {
				unsigned char WOVF:1;
				unsigned char RSTE:1;
			} BIT;
		} RSTCSR;
	} READ;
};

enum enum_ir {
IR_BSC_BUSERR=16,IR_FCU_FIFERR=21,IR_FCU_FRDYI=23,
IR_CMT0_CMI0=28,
IR_CMT1_CMI1,
IR_CMT2_CMI2,
IR_CMT3_CMI3,
IR_ICU_IRQ0=64,IR_ICU_IRQ1,IR_ICU_IRQ2,IR_ICU_IRQ3,IR_ICU_IRQ4,IR_ICU_IRQ5,IR_ICU_IRQ6,IR_ICU_IRQ7,IR_ICU_IRQ8,IR_ICU_IRQ9,IR_ICU_IRQ10,IR_ICU_IRQ11,IR_ICU_IRQ12,IR_ICU_IRQ13,IR_ICU_IRQ14,IR_ICU_IRQ15,
IR_WDT_WOVI=96,
IR_AD0_ADI0=98,
IR_AD1_ADI1,
IR_AD2_ADI2,
IR_AD3_ADI3,
IR_TPU0_TGI0A=104,IR_TPU0_TGI0B,IR_TPU0_TGI0C,IR_TPU0_TGI0D,IR_TPU0_TCI0V,
IR_TPU1_TGI1A=111,IR_TPU1_TGI1B,IR_TPU1_TCI1V=115,IR_TPU1_TCI1U,
IR_TPU2_TGI2A,IR_TPU2_TGI2B,IR_TPU2_TCI2V=120,IR_TPU2_TCI2U,
IR_TPU3_TGI3A,IR_TPU3_TGI3B,IR_TPU3_TGI3C,IR_TPU3_TGI3D,IR_TPU3_TCI3V,
IR_TPU4_TGI4A,IR_TPU4_TGI4B,IR_TPU4_TCI4V=131,IR_TPU4_TCI4U,
IR_TPU5_TGI5A,IR_TPU5_TGI5B,IR_TPU5_TCI5V=136,IR_TPU5_TCI5U,
IR_TPU6_TGI6A,IR_TPU6_TGI6B,IR_TPU6_TGI6C,IR_TPU6_TGI6D,IR_TPU6_TCI6V,
IR_TPU7_TGI7A=145,IR_TPU7_TGI7B,IR_TPU7_TCI7V=149,IR_TPU7_TCI7U,
IR_TPU8_TGI8A,IR_TPU8_TGI8B,IR_TPU8_TCI8V=154,IR_TPU8_TCI8U,
IR_TPU9_TGI9A,IR_TPU9_TGI9B,IR_TPU9_TGI9C,IR_TPU9_TGI9D,IR_TPU9_TCI9V,
IR_TPU10_TGI10A,IR_TPU10_TGI10B,IR_TPU10_TCI10V=165,IR_TPU10_TCI10U,
IR_TPU11_TGI11A,IR_TPU11_TGI11B,IR_TPU11_TCI11V=170,IR_TPU11_TCI11U,
IR_TMR0_CMIA0=174,IR_TMR0_CMIB0,IR_TMR0_OVI0,
IR_TMR1_CMIA1,IR_TMR1_CMIB1,IR_TMR1_OVI1,
IR_TMR2_CMIA2,IR_TMR2_CMIB2,IR_TMR2_OVI2,
IR_TMR3_CMIA3,IR_TMR3_CMIB3,IR_TMR3_OVI3,
IR_DMAC_DMTEND0=198,IR_DMAC_DMTEND1,IR_DMAC_DMTEND2,IR_DMAC_DMTEND3,
IR_SCI0_ERI0=214,IR_SCI0_RXI0,IR_SCI0_TXI0,IR_SCI0_TEI0,
IR_SCI1_ERI1,IR_SCI1_RXI1,IR_SCI1_TXI1,IR_SCI1_TEI1,
IR_SCI2_ERI2,IR_SCI2_RXI2,IR_SCI2_TXI2,IR_SCI2_TEI2,
IR_SCI3_ERI3,IR_SCI3_RXI3,IR_SCI3_TXI3,IR_SCI3_TEI3,
IR_SCI4_ERI4,IR_SCI4_RXI4,IR_SCI4_TXI4,IR_SCI4_TEI4,
IR_SCI5_ERI5,IR_SCI5_RXI5,IR_SCI5_TXI5,IR_SCI5_TEI5,
IR_SCI6_ERI6,IR_SCI6_RXI6,IR_SCI6_TXI6,IR_SCI6_TEI6,
IR_RIIC0_ICEEI0=246,IR_RIIC0_ICRXI0,IR_RIIC0_ICTXI0,IR_RIIC0_ICTEI0,
IR_RIIC1_ICEEI1,IR_RIIC1_ICRXI1,IR_RIIC1_ICTXI1,IR_RIIC1_ICTEI1
};

enum enum_isel {
ISEL_CMT0_CMI0=28,
ISEL_CMT1_CMI1,
ISEL_CMT2_CMI2,
ISEL_CMT3_CMI3,
ISEL_ICU_IRQ0=64,ISEL_ICU_IRQ1,ISEL_ICU_IRQ2,ISEL_ICU_IRQ3,ISEL_ICU_IRQ4,ISEL_ICU_IRQ5,ISEL_ICU_IRQ6,ISEL_ICU_IRQ7,ISEL_ICU_IRQ8,ISEL_ICU_IRQ9,ISEL_ICU_IRQ10,ISEL_ICU_IRQ11,ISEL_ICU_IRQ12,ISEL_ICU_IRQ13,ISEL_ICU_IRQ14,ISEL_ICU_IRQ15,
ISEL_AD0_ADI0=98,
ISEL_AD1_ADI1,
ISEL_AD2_ADI2,
ISEL_AD3_ADI3,
ISEL_TPU0_TGI0A=104,ISEL_TPU0_TGI0B,ISEL_TPU0_TGI0C,ISEL_TPU0_TGI0D,
ISEL_TPU1_TGI1A=111,ISEL_TPU1_TGI1B,
ISEL_TPU2_TGI2A=117,ISEL_TPU2_TGI2B,
ISEL_TPU3_TGI3A=122,ISEL_TPU3_TGI3B,ISEL_TPU3_TGI3C,ISEL_TPU3_TGI3D,
ISEL_TPU4_TGI4A=127,ISEL_TPU4_TGI4B,
ISEL_TPU5_TGI5A=133,ISEL_TPU5_TGI5B,
ISEL_TPU6_TGI6A=138,ISEL_TPU6_TGI6B,ISEL_TPU6_TGI6C,ISEL_TPU6_TGI6D,
ISEL_TPU7_TGI7A=145,ISEL_TPU7_TGI7B,
ISEL_TPU8_TGI8A=151,ISEL_TPU8_TGI8B,
ISEL_TPU9_TGI9A=156,ISEL_TPU9_TGI9B,ISEL_TPU9_TGI9C,ISEL_TPU9_TGI9D,
ISEL_TPU10_TGI10A=161,ISEL_TPU10_TGI10B,
ISEL_TPU11_TGI11A=167,ISEL_TPU11_TGI11B,
ISEL_TMR0_CMIA0=174,ISEL_TMR0_CMIB0,
ISEL_TMR1_CMIA1=177,ISEL_TMR1_CMIB1,
ISEL_TMR2_CMIA2=180,ISEL_TMR2_CMIB2,
ISEL_TMR3_CMIA3=183,ISEL_TMR3_CMIB3,
ISEL_DMAC_DMTEND0=198,ISEL_DMAC_DMTEND1,ISEL_DMAC_DMTEND2,ISEL_DMAC_DMTEND3,
ISEL_SCI0_RXI0=215,ISEL_SCI0_TXI0,
ISEL_SCI1_RXI1=219,ISEL_SCI1_TXI1,
ISEL_SCI2_RXI2=223,ISEL_SCI2_TXI2,
ISEL_SCI3_RXI3=227,ISEL_SCI3_TXI3,
ISEL_SCI4_RXI4=231,ISEL_SCI4_TXI4,
ISEL_SCI5_RXI5=235,ISEL_SCI5_TXI5,
ISEL_SCI6_RXI6=239,ISEL_SCI6_TXI6,
ISEL_RIIC0_ICRXI0=247,ISEL_RIIC0_ICTXI0,
ISEL_RIIC1_ICRXI1=251,ISEL_RIIC1_ICTXI1
};

enum enum_ier {
IER_BSC_BUSERR=0x02,
IER_FCU_FIFERR=0x02,IER_FCU_FRDYI=0x02,
IER_CMT0_CMI0=0x03,
IER_CMT1_CMI1=0x03,
IER_CMT2_CMI2=0x03,
IER_CMT3_CMI3=0x03,
IER_ICU_IRQ0=0x08,IER_ICU_IRQ1=0x08,IER_ICU_IRQ2=0x08,IER_ICU_IRQ3=0x08,IER_ICU_IRQ4=0x08,IER_ICU_IRQ5=0x08,IER_ICU_IRQ6=0x08,IER_ICU_IRQ7=0x08,IER_ICU_IRQ8=0x09,IER_ICU_IRQ9=0x09,IER_ICU_IRQ10=0x09,IER_ICU_IRQ11=0x09,IER_ICU_IRQ12=0x09,IER_ICU_IRQ13=0x09,IER_ICU_IRQ14=0x09,IER_ICU_IRQ15=0x09,
IER_WDT_WOVI=0x0C,
IER_AD0_ADI0=0x0C,
IER_AD1_ADI1=0x0C,
IER_AD2_ADI2=0x0C,
IER_AD3_ADI3=0x0C,
IER_TPU0_TGI0A=0x0D,IER_TPU0_TGI0B=0x0D,IER_TPU0_TGI0C=0x0D,IER_TPU0_TGI0D=0x0D,IER_TPU0_TCI0V=0x0D,
IER_TPU1_TGI1A=0x0D,IER_TPU1_TGI1B=0x0E,IER_TPU1_TCI1V=0x0E,IER_TPU1_TCI1U=0x0E,
IER_TPU2_TGI2A=0x0E,IER_TPU2_TGI2B=0x0E,IER_TPU2_TCI2V=0x0F,IER_TPU2_TCI2U=0x0F,
IER_TPU3_TGI3A=0x0F,IER_TPU3_TGI3B=0x0F,IER_TPU3_TGI3C=0x0F,IER_TPU3_TGI3D=0x0F,IER_TPU3_TCI3V=0x0F,
IER_TPU4_TGI4A=0x0F,IER_TPU4_TGI4B=0x10,IER_TPU4_TCI4V=0x10,IER_TPU4_TCI4U=0x10,
IER_TPU5_TGI5A=0x10,IER_TPU5_TGI5B=0x10,IER_TPU5_TCI5V=0x11,IER_TPU5_TCI5U=0x11,
IER_TPU6_TGI6A=0x11,IER_TPU6_TGI6B=0x11,IER_TPU6_TGI6C=0x11,IER_TPU6_TGI6D=0x11,IER_TPU6_TCI6V=0x11,
IER_TPU7_TGI7A=0x12,IER_TPU7_TGI7B=0x12,IER_TPU7_TCI7V=0x12,IER_TPU7_TCI7U=0x12,
IER_TPU8_TGI8A=0x12,IER_TPU8_TGI8B=0x13,IER_TPU8_TCI8V=0x13,IER_TPU8_TCI8U=0x13,
IER_TPU9_TGI9A=0x13,IER_TPU9_TGI9B=0x13,IER_TPU9_TGI9C=0x13,IER_TPU9_TGI9D=0x13,IER_TPU9_TCI9V=0x14,
IER_TPU10_TGI10A=0x14,IER_TPU10_TGI10B=0x14,IER_TPU10_TCI10V=0x14,IER_TPU10_TCI10U=0x14,
IER_TPU11_TGI11A=0x14,IER_TPU11_TGI11B=0x15,IER_TPU11_TCI11V=0x15,IER_TPU11_TCI11U=0x15,
IER_TMR0_CMIA0=0x15,IER_TMR0_CMIB0=0x15,IER_TMR0_OVI0=0x16,
IER_TMR1_CMIA1=0x16,IER_TMR1_CMIB1=0x16,IER_TMR1_OVI1=0x16,
IER_TMR2_CMIA2=0x16,IER_TMR2_CMIB2=0x16,IER_TMR2_OVI2=0x16,
IER_TMR3_CMIA3=0x16,IER_TMR3_CMIB3=0x17,IER_TMR3_OVI3=0x17,
IER_DMAC_DMTEND0=0x18,IER_DMAC_DMTEND1=0x18,IER_DMAC_DMTEND2=0x19,IER_DMAC_DMTEND3=0x19,
IER_SCI0_ERI0=0x1A,IER_SCI0_RXI0=0x1A,IER_SCI0_TXI0=0x1B,IER_SCI0_TEI0=0x1B,
IER_SCI1_ERI1=0x1B,IER_SCI1_RXI1=0x1B,IER_SCI1_TXI1=0x1B,IER_SCI1_TEI1=0x1B,
IER_SCI2_ERI2=0x1B,IER_SCI2_RXI2=0x1B,IER_SCI2_TXI2=0x1C,IER_SCI2_TEI2=0x1C,
IER_SCI3_ERI3=0x1C,IER_SCI3_RXI3=0x1C,IER_SCI3_TXI3=0x1C,IER_SCI3_TEI3=0x1C,
IER_SCI4_ERI4=0x1C,IER_SCI4_RXI4=0x1C,IER_SCI4_TXI4=0x1D,IER_SCI4_TEI4=0x1D,
IER_SCI5_ERI5=0x1D,IER_SCI5_RXI5=0x1D,IER_SCI5_TXI5=0x1D,IER_SCI5_TEI5=0x1D,
IER_SCI6_ERI6=0x1D,IER_SCI6_RXI6=0x1D,IER_SCI6_TXI6=0x1E,IER_SCI6_TEI6=0x1E,
IER_RIIC0_ICEEI0=0x1E,IER_RIIC0_ICRXI0=0x1E,IER_RIIC0_ICTXI0=0x1F,IER_RIIC0_ICTEI0=0x1F,
IER_RIIC1_ICEEI1=0x1F,IER_RIIC1_ICRXI1=0x1F,IER_RIIC1_ICTXI1=0x1F,IER_RIIC1_ICTEI1=0x1F
};

enum enum_ipr {
IPR_BSC_BUSERR=0x00,
IPR_FCU_FIFERR=0x01,IPR_FCU_FRDYI=0x02,
IPR_CMT0_CMI0=0x04,
IPR_CMT1_CMI1=0x05,
IPR_CMT2_CMI2=0x06,
IPR_CMT3_CMI3=0x07,
IPR_ICU_IRQ0=0x20,IPR_ICU_IRQ1=0x21,IPR_ICU_IRQ2=0x22,IPR_ICU_IRQ3=0x23,IPR_ICU_IRQ4=0x24,IPR_ICU_IRQ5=0x25,IPR_ICU_IRQ6=0x26,IPR_ICU_IRQ7=0x27,IPR_ICU_IRQ8=0x28,IPR_ICU_IRQ9=0x29,IPR_ICU_IRQ10=0x2A,IPR_ICU_IRQ11=0x2B,IPR_ICU_IRQ12=0x2C,IPR_ICU_IRQ13=0x2D,IPR_ICU_IRQ14=0x2E,IPR_ICU_IRQ15=0x2F,
IPR_WDT_WOVI=0x40,
IPR_AD0_ADI0=0x44,
IPR_AD1_ADI1=0x45,
IPR_AD2_ADI2=0x46,
IPR_AD3_ADI3=0x47,
IPR_TPU0_TGI0A=0x4C,IPR_TPU0_TGI0B=0x4C,IPR_TPU0_TGI0C=0x4C,IPR_TPU0_TGI0D=0x4C,IPR_TPU0_TCI0V=0x4D,
IPR_TPU1_TGI1A=0x4E,IPR_TPU1_TGI1B=0x4E,IPR_TPU1_TCI1V=0x4F,IPR_TPU1_TCI1U=0x4F,
IPR_TPU2_TGI2A=0x50,IPR_TPU2_TGI2B=0x50,IPR_TPU2_TCI2V=0x51,IPR_TPU2_TCI2U=0x51,
IPR_TPU3_TGI3A=0x52,IPR_TPU3_TGI3B=0x52,IPR_TPU3_TGI3C=0x52,IPR_TPU3_TGI3D=0x52,IPR_TPU3_TCI3V=0x53,
IPR_TPU4_TGI4A=0x54,IPR_TPU4_TGI4B=0x54,IPR_TPU4_TCI4V=0x55,IPR_TPU4_TCI4U=0x55,
IPR_TPU5_TGI5A=0x56,IPR_TPU5_TGI5B=0x56,IPR_TPU5_TCI5V=0x57,IPR_TPU5_TCI5U=0x57,
IPR_TPU6_TGI6A=0x58,IPR_TPU6_TGI6B=0x58,IPR_TPU6_TGI6C=0x58,IPR_TPU6_TGI6D=0x58,IPR_TPU6_TCI6V=0x59,
IPR_TPU7_TGI7A=0x5A,IPR_TPU7_TGI7B=0x5A,IPR_TPU7_TCI7V=0x5B,IPR_TPU7_TCI7U=0x5B,
IPR_TPU8_TGI8A=0x5C,IPR_TPU8_TGI8B=0x5C,IPR_TPU8_TCI8V=0x5D,IPR_TPU8_TCI8U=0x5D,
IPR_TPU9_TGI9A=0x5E,IPR_TPU9_TGI9B=0x5E,IPR_TPU9_TGI9C=0x5E,IPR_TPU9_TGI9D=0x5E,IPR_TPU9_TCI9V=0x5F,
IPR_TPU10_TGI10A=0x60,IPR_TPU10_TGI10B=0x60,IPR_TPU10_TCI10V=0x61,IPR_TPU10_TCI10U=0x61,
IPR_TPU11_TGI11A=0x62,IPR_TPU11_TGI11B=0x62,IPR_TPU11_TCI11V=0x63,IPR_TPU11_TCI11U=0x63,
IPR_TMR0_CMIA0=0x68,IPR_TMR0_CMIB0=0x68,IPR_TMR0_OVI0=0x68,
IPR_TMR1_CMIA1=0x69,IPR_TMR1_CMIB1=0x69,IPR_TMR1_OVI1=0x69,
IPR_TMR2_CMIA2=0x6A,IPR_TMR2_CMIB2=0x6A,IPR_TMR2_OVI2=0x6A,
IPR_TMR3_CMIA3=0x6B,IPR_TMR3_CMIB3=0x6B,IPR_TMR3_OVI3=0x6B,
IPR_DMAC_DMTEND0=0x70,IPR_DMAC_DMTEND1=0x71,IPR_DMAC_DMTEND2=0x72,IPR_DMAC_DMTEND3=0x73,
IPR_SCI0_ERI0=0x80,IPR_SCI0_RXI0=0x80,IPR_SCI0_TXI0=0x80,IPR_SCI0_TEI0=0x80,
IPR_SCI1_ERI1=0x81,IPR_SCI1_RXI1=0x81,IPR_SCI1_TXI1=0x81,IPR_SCI1_TEI1=0x81,
IPR_SCI2_ERI2=0x82,IPR_SCI2_RXI2=0x82,IPR_SCI2_TXI2=0x82,IPR_SCI2_TEI2=0x82,
IPR_SCI3_ERI3=0x83,IPR_SCI3_RXI3=0x83,IPR_SCI3_TXI3=0x83,IPR_SCI3_TEI3=0x83,
IPR_SCI4_ERI4=0x84,IPR_SCI4_RXI4=0x84,IPR_SCI4_TXI4=0x84,IPR_SCI4_TEI4=0x84,
IPR_SCI5_ERI5=0x85,IPR_SCI5_RXI5=0x85,IPR_SCI5_TXI5=0x85,IPR_SCI5_TEI5=0x85,
IPR_SCI6_ERI6=0x86,IPR_SCI6_RXI6=0x86,IPR_SCI6_TXI6=0x86,IPR_SCI6_TEI6=0x86,
IPR_RIIC0_ICEEI0=0x88,IPR_RIIC0_ICRXI0=0x89,IPR_RIIC0_ICTXI0=0x8A,IPR_RIIC0_ICTEI0=0x8B,
IPR_RIIC1_ICEEI1=0x8C,IPR_RIIC1_ICRXI1=0x8D,IPR_RIIC1_ICTXI1=0x8E,IPR_RIIC1_ICTEI1=0x8F,
IPR_BSC_=0x00,
IPR_CMT0_=0x04,
IPR_CMT1_=0x05,
IPR_CMT2_=0x06,
IPR_CMT3_=0x07,
IPR_WDT_=0x40,
IPR_AD0_=0x44,
IPR_AD1_=0x45,
IPR_AD2_=0x46,
IPR_AD3_=0x47,
IPR_TPU0_TGI=0x4C,
IPR_TPU1_TGI=0x4E,
IPR_TPU1_TCI=0x4F,
IPR_TPU2_TGI=0x50,
IPR_TPU2_TCI=0x51,
IPR_TPU3_TGI=0x52,
IPR_TPU4_TGI=0x54,
IPR_TPU4_TCI=0x55,
IPR_TPU5_TGI=0x56,
IPR_TPU5_TCI=0x57,
IPR_TPU6_TGI=0x58,
IPR_TPU7_TGI=0x5A,
IPR_TPU7_TCI=0x5B,
IPR_TPU8_TGI=0x5C,
IPR_TPU8_TCI=0x5D,
IPR_TPU9_TGI=0x5E,
IPR_TPU10_TGI=0x60,
IPR_TPU10_TCI=0x61,
IPR_TPU11_TGI=0x62,
IPR_TPU11_TCI=0x63,
IPR_TMR0_=0x68,
IPR_TMR1_=0x69,
IPR_TMR2_=0x6A,
IPR_TMR3_=0x6B,
IPR_SCI0_=0x80,
IPR_SCI1_=0x81,
IPR_SCI2_=0x82,
IPR_SCI3_=0x83,
IPR_SCI4_=0x84,
IPR_SCI5_=0x85,
IPR_SCI6_=0x86
};

#define	IEN_BSC_BUSERR		IEN0
#define	IEN_FCU_FIFERR		IEN5
#define	IEN_FCU_FRDYI		IEN7
#define	IEN_CMT0_CMI0		IEN4
#define	IEN_CMT1_CMI1		IEN5
#define	IEN_CMT2_CMI2		IEN6
#define	IEN_CMT3_CMI3		IEN7
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
#define	IEN_WDT_WOVI		IEN0
#define	IEN_AD0_ADI0		IEN2
#define	IEN_AD1_ADI1		IEN3
#define	IEN_AD2_ADI2		IEN4
#define	IEN_AD3_ADI3		IEN5
#define	IEN_TPU0_TGI0A		IEN0
#define	IEN_TPU0_TGI0B		IEN1
#define	IEN_TPU0_TGI0C		IEN2
#define	IEN_TPU0_TGI0D		IEN3
#define	IEN_TPU0_TCI0V		IEN4
#define	IEN_TPU1_TGI1A		IEN7
#define	IEN_TPU1_TGI1B		IEN0
#define	IEN_TPU1_TCI1V		IEN3
#define	IEN_TPU1_TCI1U		IEN4
#define	IEN_TPU2_TGI2A		IEN5
#define	IEN_TPU2_TGI2B		IEN6
#define	IEN_TPU2_TCI2V		IEN0
#define	IEN_TPU2_TCI2U		IEN1
#define	IEN_TPU3_TGI3A		IEN2
#define	IEN_TPU3_TGI3B		IEN3
#define	IEN_TPU3_TGI3C		IEN4
#define	IEN_TPU3_TGI3D		IEN5
#define	IEN_TPU3_TCI3V		IEN6
#define	IEN_TPU4_TGI4A		IEN7
#define	IEN_TPU4_TGI4B		IEN0
#define	IEN_TPU4_TCI4V		IEN3
#define	IEN_TPU4_TCI4U		IEN4
#define	IEN_TPU5_TGI5A		IEN5
#define	IEN_TPU5_TGI5B		IEN6
#define	IEN_TPU5_TCI5V		IEN0
#define	IEN_TPU5_TCI5U		IEN1
#define	IEN_TPU6_TGI6A		IEN2
#define	IEN_TPU6_TGI6B		IEN3
#define	IEN_TPU6_TGI6C		IEN4
#define	IEN_TPU6_TGI6D		IEN5
#define	IEN_TPU6_TCI6V		IEN6
#define	IEN_TPU7_TGI7A		IEN1
#define	IEN_TPU7_TGI7B		IEN2
#define	IEN_TPU7_TCI7V		IEN5
#define	IEN_TPU7_TCI7U		IEN6
#define	IEN_TPU8_TGI8A		IEN7
#define	IEN_TPU8_TGI8B		IEN0
#define	IEN_TPU8_TCI8V		IEN2
#define	IEN_TPU8_TCI8U		IEN3
#define	IEN_TPU9_TGI9A		IEN4
#define	IEN_TPU9_TGI9B		IEN5
#define	IEN_TPU9_TGI9C		IEN6
#define	IEN_TPU9_TGI9D		IEN7
#define	IEN_TPU9_TCI9V		IEN0
#define	IEN_TPU10_TGI10A	IEN1
#define	IEN_TPU10_TGI10B	IEN2
#define	IEN_TPU10_TCI10V	IEN5
#define	IEN_TPU10_TCI10U	IEN6
#define	IEN_TPU11_TGI11A	IEN7
#define	IEN_TPU11_TGI11B	IEN0
#define	IEN_TPU11_TCI11V	IEN2
#define	IEN_TPU11_TCI11U	IEN3
#define	IEN_TMR0_CMIA0		IEN6
#define	IEN_TMR0_CMIB0		IEN7
#define	IEN_TMR0_OVI0		IEN0
#define	IEN_TMR1_CMIA1		IEN1
#define	IEN_TMR1_CMIB1		IEN2
#define	IEN_TMR1_OVI1		IEN3
#define	IEN_TMR2_CMIA2		IEN4
#define	IEN_TMR2_CMIB2		IEN5
#define	IEN_TMR2_OVI2		IEN6
#define	IEN_TMR3_CMIA3		IEN7
#define	IEN_TMR3_CMIB3		IEN0
#define	IEN_TMR3_OVI3		IEN1
#define	IEN_DMAC_DMTEND0	IEN6
#define	IEN_DMAC_DMTEND1	IEN7
#define	IEN_DMAC_DMTEND2	IEN0
#define	IEN_DMAC_DMTEND3	IEN1
#define	IEN_SCI0_ERI0		IEN6
#define	IEN_SCI0_RXI0		IEN7
#define	IEN_SCI0_TXI0		IEN0
#define	IEN_SCI0_TEI0		IEN1
#define	IEN_SCI1_ERI1		IEN2
#define	IEN_SCI1_RXI1		IEN3
#define	IEN_SCI1_TXI1		IEN4
#define	IEN_SCI1_TEI1		IEN5
#define	IEN_SCI2_ERI2		IEN6
#define	IEN_SCI2_RXI2		IEN7
#define	IEN_SCI2_TXI2		IEN0
#define	IEN_SCI2_TEI2		IEN1
#define	IEN_SCI3_ERI3		IEN2
#define	IEN_SCI3_RXI3		IEN3
#define	IEN_SCI3_TXI3		IEN4
#define	IEN_SCI3_TEI3		IEN5
#define	IEN_SCI4_ERI4		IEN6
#define	IEN_SCI4_RXI4		IEN7
#define	IEN_SCI4_TXI4		IEN0
#define	IEN_SCI4_TEI4		IEN1
#define	IEN_SCI5_ERI5		IEN2
#define	IEN_SCI5_RXI5		IEN3
#define	IEN_SCI5_TXI5		IEN4
#define	IEN_SCI5_TEI5		IEN5
#define	IEN_SCI6_ERI6		IEN6
#define	IEN_SCI6_RXI6		IEN7
#define	IEN_SCI6_TXI6		IEN0
#define	IEN_SCI6_TEI6		IEN1
#define	IEN_RIIC0_ICEEI0	IEN6
#define	IEN_RIIC0_ICRXI0	IEN7
#define	IEN_RIIC0_ICTXI0	IEN0
#define	IEN_RIIC0_ICTEI0	IEN1
#define	IEN_RIIC1_ICEEI1	IEN2
#define	IEN_RIIC1_ICRXI1	IEN3
#define	IEN_RIIC1_ICTXI1	IEN4
#define	IEN_RIIC1_ICTEI1	IEN5

#define	VECT_BSC_BUSERR		16
#define	VECT_FCU_FIFERR		21
#define	VECT_FCU_FRDYI		23
#define	VECT_CMT0_CMI0		28
#define	VECT_CMT1_CMI1		29
#define	VECT_CMT2_CMI2		30
#define	VECT_CMT3_CMI3		31
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
#define	VECT_WDT_WOVI		96
#define	VECT_AD0_ADI0		98
#define	VECT_AD1_ADI1		99
#define	VECT_AD2_ADI2		100
#define	VECT_AD3_ADI3		101
#define	VECT_TPU0_TGI0A		104
#define	VECT_TPU0_TGI0B		105
#define	VECT_TPU0_TGI0C		106
#define	VECT_TPU0_TGI0D		107
#define	VECT_TPU0_TCI0V		108
#define	VECT_TPU1_TGI1A		111
#define	VECT_TPU1_TGI1B		112
#define	VECT_TPU1_TCI1V		115
#define	VECT_TPU1_TCI1U		116
#define	VECT_TPU2_TGI2A		117
#define	VECT_TPU2_TGI2B		118
#define	VECT_TPU2_TCI2V		120
#define	VECT_TPU2_TCI2U		121
#define	VECT_TPU3_TGI3A		122
#define	VECT_TPU3_TGI3B		123
#define	VECT_TPU3_TGI3C		124
#define	VECT_TPU3_TGI3D		125
#define	VECT_TPU3_TCI3V		126
#define	VECT_TPU4_TGI4A		127
#define	VECT_TPU4_TGI4B		128
#define	VECT_TPU4_TCI4V		131
#define	VECT_TPU4_TCI4U		132
#define	VECT_TPU5_TGI5A		133
#define	VECT_TPU5_TGI5B		134
#define	VECT_TPU5_TCI5V		136
#define	VECT_TPU5_TCI5U		137
#define	VECT_TPU6_TGI6A		138
#define	VECT_TPU6_TGI6B		139
#define	VECT_TPU6_TGI6C		140
#define	VECT_TPU6_TGI6D		141
#define	VECT_TPU6_TCI6V		142
#define	VECT_TPU7_TGI7A		145
#define	VECT_TPU7_TGI7B		146
#define	VECT_TPU7_TCI7V		149
#define	VECT_TPU7_TCI7U		150
#define	VECT_TPU8_TGI8A		151
#define	VECT_TPU8_TGI8B		152
#define	VECT_TPU8_TCI8V		154
#define	VECT_TPU8_TCI8U		155
#define	VECT_TPU9_TGI9A		156
#define	VECT_TPU9_TGI9B		157
#define	VECT_TPU9_TGI9C		158
#define	VECT_TPU9_TGI9D		159
#define	VECT_TPU9_TCI9V		160
#define	VECT_TPU10_TGI10A	161
#define	VECT_TPU10_TGI10B	162
#define	VECT_TPU10_TCI10V	165
#define	VECT_TPU10_TCI10U	166
#define	VECT_TPU11_TGI11A	167
#define	VECT_TPU11_TGI11B	168
#define	VECT_TPU11_TCI11V	170
#define	VECT_TPU11_TCI11U	171
#define	VECT_TMR0_CMIA0		174
#define	VECT_TMR0_CMIB0		175
#define	VECT_TMR0_OVI0		176
#define	VECT_TMR1_CMIA1		177
#define	VECT_TMR1_CMIB1		178
#define	VECT_TMR1_OVI1		179
#define	VECT_TMR2_CMIA2		180
#define	VECT_TMR2_CMIB2		181
#define	VECT_TMR2_OVI2		182
#define	VECT_TMR3_CMIA3		183
#define	VECT_TMR3_CMIB3		184
#define	VECT_TMR3_OVI3		185
#define	VECT_DMAC_DMTEND0	198
#define	VECT_DMAC_DMTEND1	199
#define	VECT_DMAC_DMTEND2	200
#define	VECT_DMAC_DMTEND3	201
#define	VECT_SCI0_ERI0		214
#define	VECT_SCI0_RXI0		215
#define	VECT_SCI0_TXI0		216
#define	VECT_SCI0_TEI0		217
#define	VECT_SCI1_ERI1		218
#define	VECT_SCI1_RXI1		219
#define	VECT_SCI1_TXI1		220
#define	VECT_SCI1_TEI1		221
#define	VECT_SCI2_ERI2		222
#define	VECT_SCI2_RXI2		223
#define	VECT_SCI2_TXI2		224
#define	VECT_SCI2_TEI2		225
#define	VECT_SCI3_ERI3		226
#define	VECT_SCI3_RXI3		227
#define	VECT_SCI3_TXI3		228
#define	VECT_SCI3_TEI3		229
#define	VECT_SCI4_ERI4		230
#define	VECT_SCI4_RXI4		231
#define	VECT_SCI4_TXI4		232
#define	VECT_SCI4_TEI4		233
#define	VECT_SCI5_ERI5		234
#define	VECT_SCI5_RXI5		235
#define	VECT_SCI5_TXI5		236
#define	VECT_SCI5_TEI5		237
#define	VECT_SCI6_ERI6		238
#define	VECT_SCI6_RXI6		239
#define	VECT_SCI6_TXI6		240
#define	VECT_SCI6_TEI6		241
#define	VECT_RIIC0_ICEEI0	246
#define	VECT_RIIC0_ICRXI0	247
#define	VECT_RIIC0_ICTXI0	248
#define	VECT_RIIC0_ICTEI0	249
#define	VECT_RIIC1_ICEEI1	250
#define	VECT_RIIC1_ICRXI1	251
#define	VECT_RIIC1_ICTXI1	252
#define	VECT_RIIC1_ICTEI1	253

#define	MSTP_DMAC0	SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_DMAC1	SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_DMAC2	SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_DMAC3	SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_DMAC	SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_DTC	SYSTEM.MSTPCRA.BIT.MSTPA27
#define	MSTP_AD0	SYSTEM.MSTPCRA.BIT.MSTPA23
#define	MSTP_AD1	SYSTEM.MSTPCRA.BIT.MSTPA22
#define	MSTP_AD2	SYSTEM.MSTPCRA.BIT.MSTPA21
#define	MSTP_AD3	SYSTEM.MSTPCRA.BIT.MSTPA20
#define	MSTP_DA		SYSTEM.MSTPCRA.BIT.MSTPA19
#define	MSTP_CMT0	SYSTEM.MSTPCRA.BIT.MSTPA15
#define	MSTP_CMT1	SYSTEM.MSTPCRA.BIT.MSTPA15
#define	MSTP_CMT2	SYSTEM.MSTPCRA.BIT.MSTPA14
#define	MSTP_CMT3	SYSTEM.MSTPCRA.BIT.MSTPA14
#define	MSTP_TPUA	SYSTEM.MSTPCRA.BIT.MSTPA13
#define	MSTP_TPU0	SYSTEM.MSTPCRA.BIT.MSTPA13
#define	MSTP_TPU1	SYSTEM.MSTPCRA.BIT.MSTPA13
#define	MSTP_TPU2	SYSTEM.MSTPCRA.BIT.MSTPA13
#define	MSTP_TPU3	SYSTEM.MSTPCRA.BIT.MSTPA13
#define	MSTP_TPU4	SYSTEM.MSTPCRA.BIT.MSTPA13
#define	MSTP_TPU5	SYSTEM.MSTPCRA.BIT.MSTPA13
#define	MSTP_TPUB	SYSTEM.MSTPCRA.BIT.MSTPA12
#define	MSTP_TPU6	SYSTEM.MSTPCRA.BIT.MSTPA12
#define	MSTP_TPU7	SYSTEM.MSTPCRA.BIT.MSTPA12
#define	MSTP_TPU8	SYSTEM.MSTPCRA.BIT.MSTPA12
#define	MSTP_TPU9	SYSTEM.MSTPCRA.BIT.MSTPA12
#define	MSTP_TPU10	SYSTEM.MSTPCRA.BIT.MSTPA12
#define	MSTP_TPU11	SYSTEM.MSTPCRA.BIT.MSTPA12
#define	MSTP_PPG0	SYSTEM.MSTPCRA.BIT.MSTPA11
#define	MSTP_PPG1	SYSTEM.MSTPCRA.BIT.MSTPA10
#define	MSTP_TMR0	SYSTEM.MSTPCRA.BIT.MSTPA5
#define	MSTP_TMR1	SYSTEM.MSTPCRA.BIT.MSTPA5
#define	MSTP_TMR01	SYSTEM.MSTPCRA.BIT.MSTPA5
#define	MSTP_TMR2	SYSTEM.MSTPCRA.BIT.MSTPA4
#define	MSTP_TMR3	SYSTEM.MSTPCRA.BIT.MSTPA4
#define	MSTP_TMR23	SYSTEM.MSTPCRA.BIT.MSTPA4
#define	MSTP_SCI0	SYSTEM.MSTPCRB.BIT.MSTPB31
#define	MSTP_SMCI0	SYSTEM.MSTPCRB.BIT.MSTPB31
#define	MSTP_SCI1	SYSTEM.MSTPCRB.BIT.MSTPB30
#define	MSTP_SMCI1	SYSTEM.MSTPCRB.BIT.MSTPB30
#define	MSTP_SCI2	SYSTEM.MSTPCRB.BIT.MSTPB29
#define	MSTP_SMCI2	SYSTEM.MSTPCRB.BIT.MSTPB29
#define	MSTP_SCI3	SYSTEM.MSTPCRB.BIT.MSTPB28
#define	MSTP_SMCI3	SYSTEM.MSTPCRB.BIT.MSTPB28
#define	MSTP_SCI4	SYSTEM.MSTPCRB.BIT.MSTPB27
#define	MSTP_SMCI4	SYSTEM.MSTPCRB.BIT.MSTPB27
#define	MSTP_SCI5	SYSTEM.MSTPCRB.BIT.MSTPB26
#define	MSTP_SMCI5	SYSTEM.MSTPCRB.BIT.MSTPB26
#define	MSTP_SCI6	SYSTEM.MSTPCRB.BIT.MSTPB25
#define	MSTP_SMCI6	SYSTEM.MSTPCRB.BIT.MSTPB25
#define	MSTP_CRC	SYSTEM.MSTPCRB.BIT.MSTPB23
#define	MSTP_RIIC0	SYSTEM.MSTPCRB.BIT.MSTPB21
#define	MSTP_RIIC1	SYSTEM.MSTPCRB.BIT.MSTPB20
#define	MSTP_RAM1	SYSTEM.MSTPCRC.BIT.MSTPC1
#define	MSTP_RAM0	SYSTEM.MSTPCRC.BIT.MSTPC0

#define	__IR( x )		ICU.IR[ IR ## x ].BIT.IR
#define	 _IR( x )		__IR( x )
#define	  IR( x , y )	_IR( _ ## x ## _ ## y )
#define	__ISEL( x )		ICU.ISELR[ ISEL ## x ].BIT.ISEL
#define	 _ISEL( x )		__ISEL( x )
#define	  ISEL( x , y )	_ISEL( _ ## x ## _ ## y )
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

#define	AD0		(*(volatile struct st_ad     __evenaccess *)0x88040)
#define	AD1		(*(volatile struct st_ad     __evenaccess *)0x88060)
#define	AD2		(*(volatile struct st_ad     __evenaccess *)0x88080)
#define	AD3		(*(volatile struct st_ad     __evenaccess *)0x880A0)
#define	BSC		(*(volatile struct st_bsc    __evenaccess *)0x81300)
#define	CMT		(*(volatile struct st_cmt    __evenaccess *)0x88000)
#define	CMT0	(*(volatile struct st_cmt0   __evenaccess *)0x88002)
#define	CMT1	(*(volatile struct st_cmt0   __evenaccess *)0x88008)
#define	CMT2	(*(volatile struct st_cmt0   __evenaccess *)0x88012)
#define	CMT3	(*(volatile struct st_cmt0   __evenaccess *)0x88018)
#define	CRC		(*(volatile struct st_crc    __evenaccess *)0x88280)
#define	DA		(*(volatile struct st_da     __evenaccess *)0x880C0)
#define	DMAC	(*(volatile struct st_dmac   __evenaccess *)0x82502)
#define	DMAC0	(*(volatile struct st_dmac0  __evenaccess *)0x82000)
#define	DMAC1	(*(volatile struct st_dmac1  __evenaccess *)0x82010)
#define	DMAC2	(*(volatile struct st_dmac2  __evenaccess *)0x82020)
#define	DMAC3	(*(volatile struct st_dmac3  __evenaccess *)0x82030)
#define	DTC		(*(volatile struct st_dtc    __evenaccess *)0x87400)
#define	FLASH	(*(volatile struct st_flash  __evenaccess *)0x8C288)
#define	ICU		(*(volatile struct st_icu    __evenaccess *)0x87000)
#define	IOPORT	(*(volatile struct st_ioport __evenaccess *)0x8C100)
#define	PORT0	(*(volatile struct st_port0  __evenaccess *)0x8C000)
#define	PORT1	(*(volatile struct st_port1  __evenaccess *)0x8C001)
#define	PORT2	(*(volatile struct st_port2  __evenaccess *)0x8C002)
#define	PORT3	(*(volatile struct st_port3  __evenaccess *)0x8C003)
#define	PORT4	(*(volatile struct st_port4  __evenaccess *)0x8C004)
#define	PORT5	(*(volatile struct st_port5  __evenaccess *)0x8C005)
#define	PORT6	(*(volatile struct st_port6  __evenaccess *)0x8C006)
#define	PORT7	(*(volatile struct st_port7  __evenaccess *)0x8C007)
#define	PORT8	(*(volatile struct st_port8  __evenaccess *)0x8C008)
#define	PORT9	(*(volatile struct st_port9  __evenaccess *)0x8C009)
#define	PORTA	(*(volatile struct st_porta  __evenaccess *)0x8C00A)
#define	PORTB	(*(volatile struct st_portb  __evenaccess *)0x8C00B)
#define	PORTC	(*(volatile struct st_portc  __evenaccess *)0x8C00C)
#define	PORTD	(*(volatile struct st_portd  __evenaccess *)0x8C00D)
#define	PORTE	(*(volatile struct st_porte  __evenaccess *)0x8C00E)
#define	PORTF	(*(volatile struct st_portf  __evenaccess *)0x8C00F)
#define	PORTG	(*(volatile struct st_portg  __evenaccess *)0x8C010)
#define	PORTH	(*(volatile struct st_porth  __evenaccess *)0x8C011)
#define	PPG0	(*(volatile struct st_ppg0   __evenaccess *)0x881E6)
#define	PPG1	(*(volatile struct st_ppg1   __evenaccess *)0x881F0)
#define	RIIC0	(*(volatile struct st_riic   __evenaccess *)0x88300)
#define	RIIC1	(*(volatile struct st_riic   __evenaccess *)0x88320)
#define	SCI0	(*(volatile struct st_sci    __evenaccess *)0x88240)
#define	SCI1	(*(volatile struct st_sci    __evenaccess *)0x88248)
#define	SCI2	(*(volatile struct st_sci    __evenaccess *)0x88250)
#define	SCI3	(*(volatile struct st_sci    __evenaccess *)0x88258)
#define	SCI4	(*(volatile struct st_sci    __evenaccess *)0x88260)
#define	SCI5	(*(volatile struct st_sci    __evenaccess *)0x88268)
#define	SCI6	(*(volatile struct st_sci    __evenaccess *)0x88270)
#define	SMCI0	(*(volatile struct st_smci   __evenaccess *)0x88240)
#define	SMCI1	(*(volatile struct st_smci   __evenaccess *)0x88248)
#define	SMCI2	(*(volatile struct st_smci   __evenaccess *)0x88250)
#define	SMCI3	(*(volatile struct st_smci   __evenaccess *)0x88258)
#define	SMCI4	(*(volatile struct st_smci   __evenaccess *)0x88260)
#define	SMCI5	(*(volatile struct st_smci   __evenaccess *)0x88268)
#define	SMCI6	(*(volatile struct st_smci   __evenaccess *)0x88270)
#define	SYSTEM	(*(volatile struct st_system __evenaccess *)0x80000)
#define	TMR0	(*(volatile struct st_tmr0   __evenaccess *)0x88200)
#define	TMR1	(*(volatile struct st_tmr1   __evenaccess *)0x88201)
#define	TMR2	(*(volatile struct st_tmr0   __evenaccess *)0x88210)
#define	TMR3	(*(volatile struct st_tmr1   __evenaccess *)0x88211)
#define	TMR01	(*(volatile struct st_tmr01  __evenaccess *)0x88204)
#define	TMR23	(*(volatile struct st_tmr01  __evenaccess *)0x88214)
#define	TPU0	(*(volatile struct st_tpu0   __evenaccess *)0x88110)
#define	TPU1	(*(volatile struct st_tpu1   __evenaccess *)0x88120)
#define	TPU2	(*(volatile struct st_tpu1   __evenaccess *)0x88130)
#define	TPU3	(*(volatile struct st_tpu0   __evenaccess *)0x88140)
#define	TPU4	(*(volatile struct st_tpu1   __evenaccess *)0x88150)
#define	TPU5	(*(volatile struct st_tpu1   __evenaccess *)0x88160)
#define	TPU6	(*(volatile struct st_tpu0   __evenaccess *)0x88180)
#define	TPU7	(*(volatile struct st_tpu1   __evenaccess *)0x88190)
#define	TPU8	(*(volatile struct st_tpu1   __evenaccess *)0x881A0)
#define	TPU9	(*(volatile struct st_tpu0   __evenaccess *)0x881B0)
#define	TPU10	(*(volatile struct st_tpu1   __evenaccess *)0x881C0)
#define	TPU11	(*(volatile struct st_tpu1   __evenaccess *)0x881D0)
#define	TPUA	(*(volatile struct st_tpua   __evenaccess *)0x88100)
#define	TPUB	(*(volatile struct st_tpua   __evenaccess *)0x88170)
#define	WDT		(*(volatile union un_wdt     __evenaccess *)0x88028)
#pragma bit_order
#pragma packoption
#endif