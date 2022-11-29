/********************************************************************************/
/*                                                                              */
/* Device     : RX/RX600/RX62N                                                  */
/* File Name  : ioedfine.h                                                      */
/* Abstract   : Definition of I/O Register.                                     */
/* History    : V2.0  (2010-08-21)  [Hardware Manual Revision : 1.00]           */
/* Note       : This is a typical example.                                      */
/*                                                                              */
/*  Copyright(c) 2010 Renesas Electronics Corp.                                 */
/*                  And Renesas Solutions Corp. ,All Rights Reserved.           */
/*                                                                              */
/********************************************************************************/
/*                                                                              */
/*  DESCRIPTION : Definition of ICU Register                                    */
/*  CPU TYPE    : RX62N                                                         */
/*                                                                              */
/*  Usage : IR,DTCER,IER,IPR of ICU Register                                    */
/*     The following IR, DTCE, IEN, IPR macro functions simplify usage.         */
/*     The bit access operation is "Bit_Name(interrupt source,name)".           */
/*     A part of the name can be omitted.                                       */
/*     for example :                                                            */
/*       IR(MTU0,TGIA0) = 0;     expands to :                                   */
/*         ICU.IR[114].BIT.IR = 0;                                              */
/*                                                                              */
/*       DTCE(ICU,IRQ0) = 1;     expands to :                                   */
/*         ICU.DTCER[64].BIT.DTCE = 1;                                          */
/*                                                                              */
/*       IEN(CMT0,CMI0) = 1;     expands to :                                   */
/*         ICU.IER[0x03].BIT.IEN4 = 1;                                          */
/*                                                                              */
/*       IPR(MTU1,TGIA1) = 2;    expands to :                                   */
/*       IPR(MTU1,TGI  ) = 2;    // TGIA1,TGIB1 share IPR level.                */
/*         ICU.IPR[0x53].BIT.IPR = 2;                                           */
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
/*       #pragma interrupt INT_MTU0_TGIA0(vect=VECT(MTU0,TGIA0))  expands to :  */
/*         #pragma interrupt INT_MTU0_TGIA0(vect=114)                           */
/*                                                                              */
/*  Usage : MSTPCRA,MSTPCRB,MSTPCRC of SYSTEM Register                          */
/*     The bit access operation is "MSTP(name)".                                */
/*     The name that can be used is a macro name defined with "iodefine.h".     */
/*     for example :                                                            */
/*       MSTP(TMR2) = 0;    // TMR2,TMR3,TMR23                    expands to :  */
/*         SYSTEM.MSTPCRA.BIT.MSTPA4  = 0;                                      */
/*       MSTP(SCI0) = 0;    // SCI0,SMCI0                         expands to :  */
/*         SYSTEM.MSTPCRB.BIT.MSTPB31 = 0;                                      */
/*       MSTP(MTU4) = 0;    // MTUA,MTU0,MTU1,MTU2,MTU3,MTU4,MTU5 expands to :  */
/*         SYSTEM.MSTPCRA.BIT.MSTPA9  = 0;                                      */
/*       MSTP(CMT3) = 0;    // CMT2,CMT3                          expands to :  */
/*         SYSTEM.MSTPCRA.BIT.MSTPA14 = 0;                                      */
/*                                                                              */
/*                                                                              */
/********************************************************************************/
#ifndef __RX62NIODEFINE_HEADER__
#define __RX62NIODEFINE_HEADER__
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
	char           wk1[11];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char DIAG:2;
		} BIT;
	} ADDIAGR;
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
	char           wk1[3];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char MST:3;
			unsigned char :2;
			unsigned char TO:1;
			unsigned char IA:1;
		} BIT;
	} BERSR1;
	char           wk2[1];
	union {
		unsigned short WORD;
		struct {
			unsigned short ADDR:13;
		} BIT;
	} BERSR2;
	char           wk3[7414];
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
	} CS0WCR1;
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
	} CS0WCR2;
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
	} CS1WCR1;
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
	} CS1WCR2;
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
	} CS2WCR1;
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
	} CS2WCR2;
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
	} CS3WCR1;
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
	} CS3WCR2;
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
	} CS4WCR1;
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
	} CS4WCR2;
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
	} CS5WCR1;
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
	} CS5WCR2;
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
	} CS6WCR1;
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
	} CS6WCR2;
	char           wk10[6];
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
	} CS7WCR1;
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
	} CS7WCR2;
	char           wk11[1926];
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
	} CS0CR;
	char           wk12[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS0REC;
	char           wk13[6];
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
	} CS1CR;
	char           wk14[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS1REC;
	char           wk15[6];
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
	} CS2CR;
	char           wk16[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS2REC;
	char           wk17[6];
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
	} CS3CR;
	char           wk18[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS3REC;
	char           wk19[6];
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
	} CS4CR;
	char           wk20[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS4REC;
	char           wk21[6];
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
	} CS5CR;
	char           wk22[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS5REC;
	char           wk23[6];
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
	} CS6CR;
	char           wk24[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS6REC;
	char           wk25[6];
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
	} CS7CR;
	char           wk26[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS7REC;
	char           wk27[900];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char BSIZE:2;
			unsigned char :3;
			unsigned char EXENB:1;
		} BIT;
	} SDCCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char EMODE:1;
		} BIT;
	} SDCMOD;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char BE:1;
		} BIT;
	} SDAMOD;
	char           wk28[13];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char SFEN:1;
		} BIT;
	} SDSELF;
	char           wk29[3];
	union {
		unsigned short WORD;
		struct {
			unsigned short REFW:4;
			unsigned short RFC:12;
		} BIT;
	} SDRFCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char RFEN:1;
		} BIT;
	} SDRFEN;
	char           wk30[9];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char INIRQ:1;
		} BIT;
	} SDICR;
	char           wk31[3];
	union {
		unsigned short WORD;
		struct {
			unsigned short :5;
			unsigned short PRC:3;
			unsigned short ARFC:4;
			unsigned short ARFI:4;
		} BIT;
	} SDIR;
	char           wk32[26];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char MXC:2;
		} BIT;
	} SDADR;
	char           wk33[3];
	union {
		unsigned long LONG;
		struct {
			unsigned long :13;
			unsigned long RAS:3;
			unsigned long :2;
			unsigned long RCD:2;
			unsigned long RP:3;
			unsigned long WR:1;
			unsigned long :5;
			unsigned long CL:3;
		} BIT;
	} SDTR;
	union {
		unsigned short WORD;
		struct {
			unsigned short :1;
			unsigned short MR:15;
		} BIT;
	} SDMOD;
	char           wk34[6];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char SRFST:1;
			unsigned char INIST:1;
			unsigned char :2;
			unsigned char MRSST:1;
		} BIT;
	} SDSR;
};

struct st_can {
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
				unsigned long IDE:1;
				unsigned long RTR:1;
				unsigned long :1;
				unsigned long SID:11;
				unsigned long EID:18;
			} BIT;
		} ID;
		union {
			unsigned short WORD;
			struct {
				unsigned char H;
				unsigned char L;
			} BYTE;
			struct {
				unsigned char :8;
				unsigned char :4;
				unsigned char DLC:4;
			} BIT;
		} DLC;
		unsigned char  DATA[8];
		union {
			unsigned short WORD;
			struct {
				unsigned char TSH;
				unsigned char TSL;
			} BYTE;
		} TS;
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
			unsigned long :3;
			unsigned long SID:11;
			unsigned long EID:18;
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
			unsigned long IDE:1;
			unsigned long RTR:1;
			unsigned long :1;
			unsigned long SID:11;
			unsigned long EID:18;
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
			unsigned long IDE:1;
			unsigned long RTR:1;
			unsigned long :1;
			unsigned long SID:11;
			unsigned long EID:18;
		} BIT;
	} FIDCR1;
	unsigned long  MKIVLR;
	unsigned long  MIER;
	char           wk0[1008];
	union {
		unsigned char BYTE;
		union {
			struct {
				unsigned char TRMREQ:1;
				unsigned char RECREQ:1;
				unsigned char :1;
				unsigned char ONESHOT:1;
				unsigned char :1;
				unsigned char TRMABT:1;
				unsigned char TRMACTIVE:1;
				unsigned char SENTDATA:1;
			} TX;
			struct {
				unsigned char :5;
				unsigned char MSGLOST:1;
				unsigned char INVALDATA:1;
				unsigned char NEWDATA:1;
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
			unsigned char :2;
			unsigned char RBOC:1;
			unsigned char BOM:2;
			unsigned char SLPM:1;
			unsigned char CANM:2;
			unsigned char TSPS:2;
			unsigned char TSRC:1;
			unsigned char TPM:1;
			unsigned char MLM:1;
			unsigned char IDFM:2;
			unsigned char MBM:1;
		} BIT;
	} CTLR;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char :1;
			unsigned char RECST:1;
			unsigned char TRMST:1;
			unsigned char BOST:1;
			unsigned char EPST:1;
			unsigned char SLPST:1;
			unsigned char HLTST:1;
			unsigned char RSTST:1;
			unsigned char EST:1;
			unsigned char TABST:1;
			unsigned char FMLST:1;
			unsigned char NMLST:1;
			unsigned char TFST:1;
			unsigned char RFST:1;
			unsigned char SDST:1;
			unsigned char NDST:1;
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
			unsigned long TSEG1:4;
			unsigned long :2;
			unsigned long BRP:10;
			unsigned long :2;
			unsigned long SJW:2;
			unsigned long :1;
			unsigned long TSEG2:3;
		} BIT;
	} BCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char RFEST:1;
			unsigned char RFWST:1;
			unsigned char RFFST:1;
			unsigned char RFMLF:1;
			unsigned char RFUST:3;
			unsigned char RFE:1;
		} BIT;
	} RFCR;
	unsigned char  RFPCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char TFEST:1;
			unsigned char TFFST:1;
			unsigned char :2;
			unsigned char TFUST:3;
			unsigned char TFE:1;
		} BIT;
	} TFCR;
	unsigned char  TFPCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char BLIE:1;
			unsigned char OLIE:1;
			unsigned char ORIE:1;
			unsigned char BORIE:1;
			unsigned char BOEIE:1;
			unsigned char EPIE:1;
			unsigned char EWIE:1;
			unsigned char BEIE:1;
		} BIT;
	} EIER;
	union {
		unsigned char BYTE;
		struct {
			unsigned char BLIF:1;
			unsigned char OLIF:1;
			unsigned char ORIF:1;
			unsigned char BORIF:1;
			unsigned char BOEIF:1;
			unsigned char EPIF:1;
			unsigned char EWIF:1;
			unsigned char BEIF:1;
		} BIT;
	} EIFR;
	unsigned char  RECR;
	unsigned char  TECR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char EDPM:1;
			unsigned char ADEF:1;
			unsigned char BE0F:1;
			unsigned char BE1F:1;
			unsigned char CEF:1;
			unsigned char AEF:1;
			unsigned char FEF:1;
			unsigned char SEF:1;
		} BIT;
	} ECSR;
	unsigned char  CSSR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SEST:1;
			unsigned char :2;
			unsigned char MBNST:5;
		} BIT;
	} MSSR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char MBSM:2;
		} BIT;
	} MSMR;
	unsigned short TSR;
	unsigned short AFSR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char TSTM:2;
			unsigned char TSTE:1;
		} BIT;
	} TCR;
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
	} DMAST;
};

struct st_dmac0 {
	void          *DMSAR;
	void          *DMDAR;
	unsigned long  DMCRA;
	unsigned short DMCRB;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short MD:2;
			unsigned short DTS:2;
			unsigned short :2;
			unsigned short SZ:2;
			unsigned short :6;
			unsigned short DCTG:2;
		} BIT;
	} DMTMD;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char DTIE:1;
			unsigned char ESIE:1;
			unsigned char RPTIE:1;
			unsigned char SARIE:1;
			unsigned char DARIE:1;
		} BIT;
	} DMINT;
	union {
		unsigned short WORD;
		struct {
			unsigned short SM:2;
			unsigned short :1;
			unsigned short SARA:5;
			unsigned short DM:2;
			unsigned short :1;
			unsigned short DARA:5;
		} BIT;
	} DMAMD;
	char           wk2[2];
	unsigned long  DMOFR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DTE:1;
		} BIT;
	} DMCNT;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char CLRS:1;
			unsigned char :3;
			unsigned char SWREQ:1;
		} BIT;
	} DMREQ;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ACT:1;
			unsigned char :2;
			unsigned char DTIF:1;
			unsigned char :3;
			unsigned char ESIF:1;
		} BIT;
	} DMSTS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DISEL:1;
		} BIT;
	} DMCSL;
};

struct st_dmac1 {
	void          *DMSAR;
	void          *DMDAR;
	unsigned long  DMCRA;
	unsigned short DMCRB;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short MD:2;
			unsigned short DTS:2;
			unsigned short :2;
			unsigned short SZ:2;
			unsigned short :6;
			unsigned short DCTG:2;
		} BIT;
	} DMTMD;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char DTIE:1;
			unsigned char ESIE:1;
			unsigned char RPTIE:1;
			unsigned char SARIE:1;
			unsigned char DARIE:1;
		} BIT;
	} DMINT;
	union {
		unsigned short WORD;
		struct {
			unsigned short SM:2;
			unsigned short :1;
			unsigned short SARA:5;
			unsigned short DM:2;
			unsigned short :1;
			unsigned short DARA:5;
		} BIT;
	} DMAMD;
	char           wk2[6];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DTE:1;
		} BIT;
	} DMCNT;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char CLRS:1;
			unsigned char :3;
			unsigned char SWREQ:1;
		} BIT;
	} DMREQ;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ACT:1;
			unsigned char :2;
			unsigned char DTIF:1;
			unsigned char :3;
			unsigned char ESIF:1;
		} BIT;
	} DMSTS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DISEL:1;
		} BIT;
	} DMCSL;
};

struct st_dtc {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char RRS:1;
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
	char           wk2[1];
	union {
		unsigned short WORD;
		struct {
			unsigned short ACT:1;
			unsigned short :7;
			unsigned short VECN:8;
		} BIT;
	} DTCSTS;
};

struct st_edmac {
	union {
		unsigned long LONG;
		struct {
			unsigned long :25;
			unsigned long DE:1;
			unsigned long DL:2;
			unsigned long :3;
			unsigned long SWR:1;
		} BIT;
	} EDMR;
	char           wk0[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :31;
			unsigned long TR:1;
		} BIT;
	} EDTRR;
	char           wk1[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :31;
			unsigned long RR:1;
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
			unsigned long :1;
			unsigned long TWB:1;
			unsigned long :3;
			unsigned long TABT:1;
			unsigned long RABT:1;
			unsigned long RFCOF:1;
			unsigned long ADE:1;
			unsigned long ECI:1;
			unsigned long TC:1;
			unsigned long TDE:1;
			unsigned long TFUF:1;
			unsigned long FR:1;
			unsigned long RDE:1;
			unsigned long RFOF:1;
			unsigned long :4;
			unsigned long CND:1;
			unsigned long DLC:1;
			unsigned long CD:1;
			unsigned long TRO:1;
			unsigned long RMAF:1;
			unsigned long :2;
			unsigned long RRF:1;
			unsigned long RTLF:1;
			unsigned long RTSF:1;
			unsigned long PRE:1;
			unsigned long CERF:1;
		} BIT;
	} EESR;
	char           wk5[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :1;
			unsigned long TWBIP:1;
			unsigned long :3;
			unsigned long TABTIP:1;
			unsigned long RABTIP:1;
			unsigned long RFCOFIP:1;
			unsigned long ADEIP:1;
			unsigned long ECIIP:1;
			unsigned long TCIP:1;
			unsigned long TDEIP:1;
			unsigned long TFUFIP:1;
			unsigned long FRIP:1;
			unsigned long RDEIP:1;
			unsigned long RFOFIP:1;
			unsigned long :4;
			unsigned long CNDIP:1;
			unsigned long DLCIP:1;
			unsigned long CDIP:1;
			unsigned long TROIP:1;
			unsigned long RMAFIP:1;
			unsigned long :2;
			unsigned long RRFIP:1;
			unsigned long RTLFIP:1;
			unsigned long RTSFIP:1;
			unsigned long PREIP:1;
			unsigned long CERFIP:1;
		} BIT;
	} EESIPR;
	char           wk6[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :20;
			unsigned long CNDCE:1;
			unsigned long DLCCE:1;
			unsigned long CDCE:1;
			unsigned long TROCE:1;
			unsigned long RMAFCE:1;
			unsigned long :2;
			unsigned long RRFCE:1;
			unsigned long RTLFCE:1;
			unsigned long RTSFCE:1;
			unsigned long PRECE:1;
			unsigned long CERFCE:1;
		} BIT;
	} TRSCER;
	char           wk7[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long MFC:16;
		} BIT;
	} RMFCR;
	char           wk8[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :21;
			unsigned long TFT:11;
		} BIT;
	} TFTR;
	char           wk9[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :19;
			unsigned long TFD:5;
			unsigned long :3;
			unsigned long RFD:5;
		} BIT;
	} FDR;
	char           wk10[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :30;
			unsigned long RNC:1;
			unsigned long RNR:1;
		} BIT;
	} RMCR;
	char           wk11[8];
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long UNDER:16;
		} BIT;
	} TFUCR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long OVER:16;
		} BIT;
	} RFOCR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :31;
			unsigned long TLB:1;
		} BIT;
	} IOSR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :13;
			unsigned long RFFO:3;
			unsigned long :13;
			unsigned long RFDO:3;
		} BIT;
	} FCFTR;
	char           wk12[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :14;
			unsigned long PADS:2;
			unsigned long :10;
			unsigned long PADR:6;
		} BIT;
	} RPADIR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :27;
			unsigned long TIM:1;
			unsigned long :3;
			unsigned long TIS:1;
		} BIT;
	} TRIMD;
	char           wk13[72];
	void          *RBWAR;
	void          *RDFAR;
	char           wk14[4];
	void          *TBRAR;
	void          *TDFAR;
};

struct st_etherc {
	union {
		unsigned long LONG;
		struct {
			unsigned long :11;
			unsigned long TPC:1;
			unsigned long ZPE:1;
			unsigned long PFR:1;
			unsigned long RXF:1;
			unsigned long TXF:1;
			unsigned long :3;
			unsigned long PRCEF:1;
			unsigned long :2;
			unsigned long MPDE:1;
			unsigned long :2;
			unsigned long RE:1;
			unsigned long TE:1;
			unsigned long :1;
			unsigned long ILB:1;
			unsigned long RTM:1;
			unsigned long DM:1;
			unsigned long PRM:1;
		} BIT;
	} ECMR;
	char           wk0[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :20;
			unsigned long RFL:12;
		} BIT;
	} RFLR;
	char           wk1[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :26;
			unsigned long BFR:1;
			unsigned long PSRTO:1;
			unsigned long :1;
			unsigned long LCHNG:1;
			unsigned long MPD:1;
			unsigned long ICD:1;
		} BIT;
	} ECSR;
	char           wk2[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :26;
			unsigned long BFSIPR:1;
			unsigned long PSRTOIP:1;
			unsigned long :1;
			unsigned long LCHNGIP:1;
			unsigned long MPDIP:1;
			unsigned long ICDIP:1;
		} BIT;
	} ECSIPR;
	char           wk3[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :28;
			unsigned long MDI:1;
			unsigned long MDO:1;
			unsigned long MMD:1;
			unsigned long MDC:1;
		} BIT;
	} PIR;
	char           wk4[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :31;
			unsigned long LMON:1;
		} BIT;
	} PSR;
	char           wk5[20];
	union {
		unsigned long LONG;
		struct {
			unsigned long :12;
			unsigned long RMD:20;
		} BIT;
	} RDMLR;
	char           wk6[12];
	union {
		unsigned long LONG;
		struct {
			unsigned long :27;
			unsigned long IPG:5;
		} BIT;
	} IPGR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long AP:16;
		} BIT;
	} APR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long MP:16;
		} BIT;
	} MPR;
	char           wk7[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :24;
			unsigned long RPAUSE:8;
		} BIT;
	} RFCF;
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long TPAUSE:16;
		} BIT;
	} TPAUSER;
	union {
		unsigned long LONG;
		struct {
			unsigned long :24;
			unsigned long TXP:8;
		} BIT;
	} TPAUSECR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long BCF:16;
		} BIT;
	} BCFRR;
	char           wk8[80];
	unsigned long  MAHR;
	char           wk9[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long MA:16;
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
};

struct st_exdmac {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DMST:1;
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
};

struct st_exdmac0 {
	void          *EDMSAR;
	void          *EDMDAR;
	unsigned long  EDMCRA;
	unsigned short EDMCRB;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short MD:2;
			unsigned short DTS:2;
			unsigned short :2;
			unsigned short SZ:2;
			unsigned short :6;
			unsigned short DCTG:2;
		} BIT;
	} EDMTMD;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char DACKS:1;
			unsigned char DACKE:1;
			unsigned char DACKW:1;
		} BIT;
	} EDMOMD;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char DTIE:1;
			unsigned char ESIE:1;
			unsigned char RPTIE:1;
			unsigned char SARIE:1;
			unsigned char DARIE:1;
		} BIT;
	} EDMINT;
	union {
		unsigned long LONG;
		struct {
			unsigned long :14;
			unsigned long AMS:1;
			unsigned long DIR:1;
			unsigned long SM:2;
			unsigned long :1;
			unsigned long SARA:5;
			unsigned long DM:2;
			unsigned long :1;
			unsigned long DARA:5;
		} BIT;
	} EDMAMD;
	unsigned long  EDMOFR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DTE:1;
		} BIT;
	} EDMCNT;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char CLRS:1;
			unsigned char :3;
			unsigned char SWREQ:1;
		} BIT;
	} EDMREQ;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ACT:1;
			unsigned char :2;
			unsigned char DTIF:1;
			unsigned char :3;
			unsigned char ESIF:1;
		} BIT;
	} EDMSTS;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char DREQS:2;
		} BIT;
	} EDMRMD;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char EREQ:1;
		} BIT;
	} EDMERF;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char PREQ:1;
		} BIT;
	} EDMPRF;
};

struct st_exdmac1 {
	void          *EDMSAR;
	void          *EDMDAR;
	unsigned long  EDMCRA;
	unsigned short EDMCRB;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short MD:2;
			unsigned short DTS:2;
			unsigned short :2;
			unsigned short SZ:2;
			unsigned short :6;
			unsigned short DCTG:2;
		} BIT;
	} EDMTMD;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char DACKS:1;
			unsigned char DACKE:1;
			unsigned char DACKW:1;
		} BIT;
	} EDMOMD;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char DTIE:1;
			unsigned char ESIE:1;
			unsigned char RPTIE:1;
			unsigned char SARIE:1;
			unsigned char DARIE:1;
		} BIT;
	} EDMINT;
	union {
		unsigned long LONG;
		struct {
			unsigned long :14;
			unsigned long AMS:1;
			unsigned long DIR:1;
			unsigned long SM:2;
			unsigned long :1;
			unsigned long SARA:5;
			unsigned long DM:2;
			unsigned long :1;
			unsigned long DARA:5;
		} BIT;
	} EDMAMD;
	char           wk1[4];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DTE:1;
		} BIT;
	} EDMCNT;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char CLRS:1;
			unsigned char :3;
			unsigned char SWREQ:1;
		} BIT;
	} EDMREQ;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ACT:1;
			unsigned char :2;
			unsigned char DTIF:1;
			unsigned char :3;
			unsigned char ESIF:1;
		} BIT;
	} EDMSTS;
	char           wk2[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char DREQS:2;
		} BIT;
	} EDMRMD;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char EREQ:1;
		} BIT;
	} EDMERF;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char PREQ:1;
		} BIT;
	} EDMPRF;
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
			unsigned short DBRE07:1;
			unsigned short DBRE06:1;
			unsigned short DBRE05:1;
			unsigned short DBRE04:1;
			unsigned short DBRE03:1;
			unsigned short DBRE02:1;
			unsigned short DBRE01:1;
			unsigned short DBRE00:1;
		} BIT;
	} DFLRE0;
	union {
		unsigned short WORD;
		struct {
			unsigned short KEY:8;
			unsigned short DBRE15:1;
			unsigned short DBRE14:1;
			unsigned short DBRE13:1;
			unsigned short DBRE12:1;
			unsigned short DBRE11:1;
			unsigned short DBRE10:1;
			unsigned short DBRE09:1;
			unsigned short DBRE08:1;
		} BIT;
	} DFLRE1;
	char           wk4[12];
	union {
		unsigned short WORD;
		struct {
			unsigned short KEY:8;
			unsigned short DBWE07:1;
			unsigned short DBWE06:1;
			unsigned short DBWE05:1;
			unsigned short DBWE04:1;
			unsigned short DBWE03:1;
			unsigned short DBWE02:1;
			unsigned short DBWE01:1;
			unsigned short DBWE00:1;
		} BIT;
	} DFLWE0;
	union {
		unsigned short WORD;
		struct {
			unsigned short KEY:8;
			unsigned short DBWE15:1;
			unsigned short DBWE14:1;
			unsigned short DBWE13:1;
			unsigned short DBWE12:1;
			unsigned short DBWE11:1;
			unsigned short DBWE10:1;
			unsigned short DBWE09:1;
			unsigned short DBWE08:1;
		} BIT;
	} DFLWE1;
	union {
		unsigned short WORD;
		struct {
			unsigned short KEY:8;
			unsigned short :7;
			unsigned short FCRME:1;
		} BIT;
	} FCURAME;
	char           wk5[15194];
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
			unsigned short :6;
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
			unsigned short FPKEY:8;
			unsigned short :7;
			unsigned short FRESET:1;
		} BIT;
	} FRESETR;
	char           wk6[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short CMDR:8;
			unsigned short PCMDR:8;
		} BIT;
	} FCMDR;
	char           wk7[12];
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
			unsigned short :5;
			unsigned short BCADR:8;
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
	char           wk8[24];
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
			unsigned char :7;
			unsigned char DTCE:1;
		} BIT;
	} DTCER[255];
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
	char           wk2[192];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char SWINT:1;
		} BIT;
	} SWINTR;
	char           wk3[15];
	union {
		unsigned short WORD;
		struct {
			unsigned short FIEN:1;
			unsigned short :7;
			unsigned short FVCT:8;
		} BIT;
	} FIR;
	char           wk4[14];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char IPR:4;
		} BIT;
	} IPR[144];
	char           wk5[112];
	unsigned char  DMRSR0;
	char           wk6[3];
	unsigned char  DMRSR1;
	char           wk7[3];
	unsigned char  DMRSR2;
	char           wk8[3];
	unsigned char  DMRSR3;
	char           wk9[243];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char IRQMD:2;
		} BIT;
	} IRQCR[16];
	char           wk10[112];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char OSTST:1;
			unsigned char LVDST:1;
			unsigned char NMIST:1;
		} BIT;
	} NMISR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char OSTEN:1;
			unsigned char LVDEN:1;
			unsigned char NMIEN:1;
		} BIT;
	} NMIER;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char OSTCLR:1;
			unsigned char :1;
			unsigned char NMICLR:1;
		} BIT;
	} NMICLR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char NMIMD:1;
		} BIT;
	} NMICR;
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
	} PF0CSE;
	union {
		unsigned char BYTE;
		struct {
			unsigned char CS7S:2;
			unsigned char CS6S:2;
			unsigned char CS5S:2;
			unsigned char CS4S:2;
		} BIT;
	} PF1CSS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char CS3S:2;
			unsigned char CS2S:2;
			unsigned char CS1S:2;
			unsigned char :1;
			unsigned char CS0S:1;
		} BIT;
	} PF2CSS;
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
	} PF3BUS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char A15E:1;
			unsigned char A14E:1;
			unsigned char A13E:1;
			unsigned char A12E:1;
			unsigned char A11E:1;
			unsigned char A10E:1;
			unsigned char ADRLE:2;
		} BIT;
	} PF4BUS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char WR32BC32E:1;
			unsigned char WR1BC1E:1;
			unsigned char DH32E:1;
			unsigned char DHE:1;
			unsigned char :2;
			unsigned char ADRHMS:1;
		} BIT;
	} PF5BUS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SDCLKE:1;
			unsigned char DQM1E:1;
			unsigned char :1;
			unsigned char MDSDE:1;
			unsigned char :2;
			unsigned char WAITS:2;
		} BIT;
	} PF6BUS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char EDMA1S:2;
			unsigned char EDMA0S:2;
		} BIT;
	} PF7DMA;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ITS15:1;
			unsigned char :1;
			unsigned char ITS13:1;
			unsigned char :1;
			unsigned char ITS11:1;
			unsigned char ITS10:1;
			unsigned char ITS9:1;
			unsigned char ITS8:1;
		} BIT;
	} PF8IRQ;
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
	} PF9IRQ;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char ADTRG0S:1;
		} BIT;
	} PFAADC;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char TMR3S:1;
			unsigned char TMR2S:1;
			unsigned char TMR1S:1;
			unsigned char TMR0S:1;
		} BIT;
	} PFBTMR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char TCLKS:1;
			unsigned char MTUS6:1;
			unsigned char MTUS5:1;
			unsigned char MTUS4:1;
			unsigned char MTUS3:1;
			unsigned char MTUS2:1;
			unsigned char MTUS1:1;
			unsigned char MTUS0:1;
		} BIT;
	} PFCMTU;
	union {
		unsigned char BYTE;
		struct {
			unsigned char TCLKS:1;
			unsigned char MTUS6:1;
		} BIT;
	} PFDMTU;
	union {
		unsigned char BYTE;
		struct {
			unsigned char EE:1;
			unsigned char :2;
			unsigned char PHYMODE:1;
			unsigned char ENETE3:1;
			unsigned char ENETE2:1;
			unsigned char ENETE1:1;
			unsigned char ENETE0:1;
		} BIT;
	} PFENET;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char SCI6S:1;
			unsigned char :2;
			unsigned char SCI3S:1;
			unsigned char SCI2S:1;
			unsigned char SCI1S:1;
		} BIT;
	} PFFSCI;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SSL3E:1;
			unsigned char SSL2E:1;
			unsigned char SSL1E:1;
			unsigned char SSL0E:1;
			unsigned char MISOE:1;
			unsigned char MOSIE:1;
			unsigned char RSPCKE:1;
			unsigned char RSPIS:1;
		} BIT;
	} PFGSPI;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SSL3E:1;
			unsigned char SSL2E:1;
			unsigned char SSL1E:1;
			unsigned char SSL0E:1;
			unsigned char MISOE:1;
			unsigned char MOSIE:1;
			unsigned char RSPCKE:1;
			unsigned char RSPIS:1;
		} BIT;
	} PFHSPI;
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char CAN0E:1;
		} BIT;
	} PFJCAN;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char USBE:1;
			unsigned char PDHZS:1;
			unsigned char PUPHZS:1;
			unsigned char USBMD:2;
		} BIT;
	} PFKUSB;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char USBE:1;
			unsigned char PDHZS:1;
			unsigned char PUPHZS:1;
			unsigned char USBMD:2;
		} BIT;
	} PFLUSB;
	union {
		unsigned char BYTE;
		struct {
			unsigned char POE7E:1;
			unsigned char POE6E:1;
			unsigned char POE5E:1;
			unsigned char POE4E:1;
			unsigned char POE3E:1;
			unsigned char POE2E:1;
			unsigned char POE1E:1;
			unsigned char POE0E:1;
		} BIT;
	} PFMPOE;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char POE9E:1;
			unsigned char POE8E:1;
		} BIT;
	} PFNPOE;
};

struct st_iwdt {
	unsigned char  IWDTRR;
	char           wk0[1];
	union {
		unsigned short WORD;
		struct {
			unsigned short :8;
			unsigned short CKS:4;
			unsigned short :2;
			unsigned short TOPS:2;
		} BIT;
	} IWDTCR;
	union {
		unsigned short WORD;
		struct {
			unsigned short :1;
			unsigned short UNDFF:1;
			unsigned short CNTVAL:14;
		} BIT;
	} IWDTSR;
};

struct st_mtu0 {
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
			unsigned char BFE:1;
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
	char           wk0[16];
	unsigned short TGRE;
	unsigned short TGRF;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char TGIEF:1;
			unsigned char TGIEE:1;
		} BIT;
	} TIER2;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char TTSE:1;
			unsigned char TTSB:1;
			unsigned char TTSA:1;
		} BIT;
	} TBTM;
};

struct st_mtu1 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char CCLR:2;
			unsigned char CKEG:2;
			unsigned char TPSC:3;
		} BIT;
	} TCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
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
	char           wk1[4];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char I2BE:1;
			unsigned char I2AE:1;
			unsigned char I1BE:1;
			unsigned char I1AE:1;
		} BIT;
	} TICCR;
};

struct st_mtu2 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char CCLR:2;
			unsigned char CKEG:2;
			unsigned char TPSC:3;
		} BIT;
	} TCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
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

struct st_mtu3 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char CCLR:3;
			unsigned char CKEG:2;
			unsigned char TPSC:3;
		} BIT;
	} TCR;
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char BFB:1;
			unsigned char BFA:1;
			unsigned char MD:4;
		} BIT;
	} TMDR;
	char           wk1[1];
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
	char           wk2[2];
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
			unsigned char TCFD:1;
		} BIT;
	} TSR;
	char           wk7[11];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char TTSB:1;
			unsigned char TTSA:1;
		} BIT;
	} TBTM;
};

struct st_mtu4 {
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char CCLR:3;
			unsigned char CKEG:2;
			unsigned char TPSC:3;
		} BIT;
	} TCR;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char BFB:1;
			unsigned char BFA:1;
			unsigned char MD:4;
		} BIT;
	} TMDR;
	char           wk2[2];
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
	char           wk3[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char TTGE:1;
			unsigned char TTGE2:1;
			unsigned char :1;
			unsigned char TCIEV:1;
			unsigned char TGIED:1;
			unsigned char TGIEC:1;
			unsigned char TGIEB:1;
			unsigned char TGIEA:1;
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
			unsigned char TCFD:1;
		} BIT;
	} TSR;
	char           wk8[11];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char TTSB:1;
			unsigned char TTSA:1;
		} BIT;
	} TBTM;
	char           wk9[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short BF:2;
			unsigned short :6;
			unsigned short UT4AE:1;
			unsigned short DT4AE:1;
			unsigned short UT4BE:1;
			unsigned short DT4BE:1;
			unsigned short ITA3AE:1;
			unsigned short ITA4VE:1;
			unsigned short ITB3AE:1;
			unsigned short ITB4VE:1;
		} BIT;
	} TADCR;
	char           wk10[2];
	unsigned short TADCORA;
	unsigned short TADCORB;
	unsigned short TADCOBRA;
	unsigned short TADCOBRB;
};

struct st_mtu5 {
	unsigned short TCNTU;
	unsigned short TGRU;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char TPSC:2;
		} BIT;
	} TCRU;
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char IOC:5;
		} BIT;
	} TIORU;
	char           wk1[9];
	unsigned short TCNTV;
	unsigned short TGRV;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char TPSC:2;
		} BIT;
	} TCRV;
	char           wk2[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char IOC:5;
		} BIT;
	} TIORV;
	char           wk3[9];
	unsigned short TCNTW;
	unsigned short TGRW;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char TPSC:2;
		} BIT;
	} TCRW;
	char           wk4[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char IOC:5;
		} BIT;
	} TIORW;
	char           wk5[11];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char TGIE5U:1;
			unsigned char TGIE5V:1;
			unsigned char TGIE5W:1;
		} BIT;
	} TIER;
	char           wk6[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char CSTU5:1;
			unsigned char CSTV5:1;
			unsigned char CSTW5:1;
		} BIT;
	} TSTR;
	char           wk7[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char CMPCLR5U:1;
			unsigned char CMPCLR5V:1;
			unsigned char CMPCLR5W:1;
		} BIT;
	} TCNTCMPCLR;
};

struct st_mtua {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char OE4D:1;
			unsigned char OE4C:1;
			unsigned char OE3D:1;
			unsigned char OE4B:1;
			unsigned char OE4A:1;
			unsigned char OE3B:1;
		} BIT;
	} TOER;
	char           wk0[2];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char BDC:1;
			unsigned char N:1;
			unsigned char P:1;
			unsigned char FB:1;
			unsigned char WF:1;
			unsigned char VF:1;
			unsigned char UF:1;
		} BIT;
	} TGCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char PSYE:1;
			unsigned char :2;
			unsigned char TOCL:1;
			unsigned char TOCS:1;
			unsigned char OLSN:1;
			unsigned char OLSP:1;
		} BIT;
	} TOCR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char BF:2;
			unsigned char OLS3N:1;
			unsigned char OLS3P:1;
			unsigned char OLS2N:1;
			unsigned char OLS2P:1;
			unsigned char OLS1N:1;
			unsigned char OLS1P:1;
		} BIT;
	} TOCR2;
	char           wk1[4];
	unsigned short TCDR;
	unsigned short TDDR;
	char           wk2[8];
	unsigned short TCNTS;
	unsigned short TCBR;
	char           wk3[12];
	union {
		unsigned char BYTE;
		struct {
			unsigned char T3AEN:1;
			unsigned char T3ACOR:3;
			unsigned char T4VEN:1;
			unsigned char T4VCOR:3;
		} BIT;
	} TITCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char T3ACNT:3;
			unsigned char :1;
			unsigned char T4VCNT:3;
		} BIT;
	} TITCNT;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char BTE:2;
		} BIT;
	} TBTER;
	char           wk4[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char TDER:1;
		} BIT;
	} TDER;
	char           wk5[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char OLS3N:1;
			unsigned char OLS3P:1;
			unsigned char OLS2N:1;
			unsigned char OLS2P:1;
			unsigned char OLS1N:1;
			unsigned char OLS1P:1;
		} BIT;
	} TOLBR;
	char           wk6[41];
	union {
		unsigned char BYTE;
		struct {
			unsigned char CCE:1;
			unsigned char :6;
			unsigned char WRE:1;
		} BIT;
	} TWCR;
	char           wk7[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char CST4:1;
			unsigned char CST3:1;
			unsigned char :3;
			unsigned char CST2:1;
			unsigned char CST1:1;
			unsigned char CST0:1;
		} BIT;
	} TSTR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SYNC4:1;
			unsigned char SYNC3:1;
			unsigned char :3;
			unsigned char SYNC2:1;
			unsigned char SYNC1:1;
			unsigned char SYNC0:1;
		} BIT;
	} TSYR;
	char           wk8[2];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char RWE:1;
		} BIT;
	} TRWER;
};

struct st_poe {
	union {
		unsigned short WORD;
		struct {
			unsigned short POE3F:1;
			unsigned short POE2F:1;
			unsigned short POE1F:1;
			unsigned short POE0F:1;
			unsigned short :3;
			unsigned short PIE1:1;
			unsigned short POE3M:2;
			unsigned short POE2M:2;
			unsigned short POE1M:2;
			unsigned short POE0M:2;
		} BIT;
	} ICSR1;
	union {
		unsigned short WORD;
		struct {
			unsigned short OSF1:1;
			unsigned short :5;
			unsigned short OCE1:1;
			unsigned short OIE1:1;
		} BIT;
	} OCSR1;
	union {
		unsigned short WORD;
		struct {
			unsigned short POE7F:1;
			unsigned short POE6F:1;
			unsigned short POE5F:1;
			unsigned short POE4F:1;
			unsigned short :3;
			unsigned short PIE2:1;
			unsigned short POE7M:2;
			unsigned short POE6M:2;
			unsigned short POE5M:2;
			unsigned short POE4M:2;
		} BIT;
	} ICSR2;
	union {
		unsigned short WORD;
		struct {
			unsigned short OSF2:1;
			unsigned short :5;
			unsigned short OCE2:1;
			unsigned short OIE2:1;
		} BIT;
	} OCSR2;
	union {
		unsigned short WORD;
		struct {
			unsigned short :3;
			unsigned short POE8F:1;
			unsigned short :2;
			unsigned short POE8E:1;
			unsigned short PIE3:1;
			unsigned short :6;
			unsigned short POE8M:2;
		} BIT;
	} ICSR3;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char CH6HIZ:1;
			unsigned char CH910HIZ:1;
			unsigned char CH0HIZ:1;
			unsigned char CH34HIZ:1;
		} BIT;
	} SPOER;
	union {
		unsigned char BYTE;
		struct {
			unsigned char PE7ZE:1;
			unsigned char PE6ZE:1;
			unsigned char PE5ZE:1;
			unsigned char PE4ZE:1;
			unsigned char PE3ZE:1;
			unsigned char PE2ZE:1;
			unsigned char PE1ZE:1;
			unsigned char PE0ZE:1;
		} BIT;
	} POECR1;
	union {
		unsigned short WORD;
		struct {
			unsigned short :1;
			unsigned short P1CZEA:1;
			unsigned short P2CZEA:1;
			unsigned short P3CZEA:1;
			unsigned short :1;
			unsigned short P1CZEB:1;
			unsigned short P2CZEB:1;
			unsigned short P3CZEB:1;
			unsigned short :1;
			unsigned short P4CZE:1;
			unsigned short P5CZE:1;
			unsigned short P6CZE:1;
		} BIT;
	} POECR2;
	union {
		unsigned short WORD;
		struct {
			unsigned short :3;
			unsigned short POE9F:1;
			unsigned short :2;
			unsigned short POE9E:1;
			unsigned short PIE4:1;
			unsigned short :6;
			unsigned short POE9M:2;
		} BIT;
	} ICSR4;
};

struct st_port0 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char :1;
			unsigned char B5:1;
			unsigned char :1;
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
			unsigned char :1;
			unsigned char B5:1;
			unsigned char :1;
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
			unsigned char :1;
			unsigned char B5:1;
			unsigned char :1;
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
			unsigned char :1;
			unsigned char B5:1;
			unsigned char :1;
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
			unsigned char :1;
			unsigned char B5:1;
			unsigned char :1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ODR;
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
			unsigned char :3;
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
			unsigned char :3;
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
			unsigned char :3;
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
			unsigned char :3;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ODR;
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
			unsigned char :3;
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
			unsigned char :3;
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
			unsigned char :3;
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
			unsigned char :3;
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

struct st_rspi {
	union {
		unsigned char BYTE;
		struct {
			unsigned char SPRIE:1;
			unsigned char SPE:1;
			unsigned char SPTIE:1;
			unsigned char SPEIE:1;
			unsigned char MSTR:1;
			unsigned char MODFEN:1;
			unsigned char TXMD:1;
			unsigned char SPMS:1;
		} BIT;
	} SPCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char SSLP3:1;
			unsigned char SSLP2:1;
			unsigned char SSLP1:1;
			unsigned char SSLP0:1;
		} BIT;
	} SSLP;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char MOIFE:1;
			unsigned char MOIFV:1;
			unsigned char :1;
			unsigned char SPOM:1;
			unsigned char SPLP2:1;
			unsigned char SPLP:1;
		} BIT;
	} SPPCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SPRF:1;
			unsigned char :1;
			unsigned char SPTEF:1;
			unsigned char :1;
			unsigned char PERF:1;
			unsigned char MODF:1;
			unsigned char IDLNF:1;
			unsigned char OVRF:1;
		} BIT;
	} SPSR;
	union {
		unsigned long LONG;
		struct {
			unsigned short H;
			unsigned short L;
		} WORD;
	} SPDR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char SPSLN:3;
		} BIT;
	} SPSCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char SPECM:3;
			unsigned char :1;
			unsigned char SPCP:3;
		} BIT;
	} SPSSR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SPR7:1;
			unsigned char SPR6:1;
			unsigned char SPR5:1;
			unsigned char SPR4:1;
			unsigned char SPR3:1;
			unsigned char SPR2:1;
			unsigned char SPR1:1;
			unsigned char SPR0:1;
		} BIT;
	} SPBR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char SPLW:1;
			unsigned char SPRDTD:1;
			unsigned char SLSEL:2;
			unsigned char SPFC:2;
		} BIT;
	} SPDCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char SCKDL:3;
		} BIT;
	} SPCKD;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char SLNDL:3;
		} BIT;
	} SSLND;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char SPNDL:3;
		} BIT;
	} SPND;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char PTE:1;
			unsigned char SPIIE:1;
			unsigned char SPOE:1;
			unsigned char SPPE:1;
		} BIT;
	} SPCR2;
	union {
		unsigned short WORD;
		struct {
			unsigned short SCKDEN:1;
			unsigned short SLNDEN:1;
			unsigned short SPNDEN:1;
			unsigned short LSBF:1;
			unsigned short SPB:4;
			unsigned short SSLKP:1;
			unsigned short SSLA:3;
			unsigned short BRDV:2;
			unsigned short CPOL:1;
			unsigned short CPHA:1;
		} BIT;
	} SPCMD0;
	union {
		unsigned short WORD;
		struct {
			unsigned short SCKDEN:1;
			unsigned short SLNDEN:1;
			unsigned short SPNDEN:1;
			unsigned short LSBF:1;
			unsigned short SPB:4;
			unsigned short SSLKP:1;
			unsigned short SSLA:3;
			unsigned short BRDV:2;
			unsigned short CPOL:1;
			unsigned short CPHA:1;
		} BIT;
	} SPCMD1;
	union {
		unsigned short WORD;
		struct {
			unsigned short SCKDEN:1;
			unsigned short SLNDEN:1;
			unsigned short SPNDEN:1;
			unsigned short LSBF:1;
			unsigned short SPB:4;
			unsigned short SSLKP:1;
			unsigned short SSLA:3;
			unsigned short BRDV:2;
			unsigned short CPOL:1;
			unsigned short CPHA:1;
		} BIT;
	} SPCMD2;
	union {
		unsigned short WORD;
		struct {
			unsigned short SCKDEN:1;
			unsigned short SLNDEN:1;
			unsigned short SPNDEN:1;
			unsigned short LSBF:1;
			unsigned short SPB:4;
			unsigned short SSLKP:1;
			unsigned short SSLA:3;
			unsigned short BRDV:2;
			unsigned short CPOL:1;
			unsigned short CPHA:1;
		} BIT;
	} SPCMD3;
	union {
		unsigned short WORD;
		struct {
			unsigned short SCKDEN:1;
			unsigned short SLNDEN:1;
			unsigned short SPNDEN:1;
			unsigned short LSBF:1;
			unsigned short SPB:4;
			unsigned short SSLKP:1;
			unsigned short SSLA:3;
			unsigned short BRDV:2;
			unsigned short CPOL:1;
			unsigned short CPHA:1;
		} BIT;
	} SPCMD4;
	union {
		unsigned short WORD;
		struct {
			unsigned short SCKDEN:1;
			unsigned short SLNDEN:1;
			unsigned short SPNDEN:1;
			unsigned short LSBF:1;
			unsigned short SPB:4;
			unsigned short SSLKP:1;
			unsigned short SSLA:3;
			unsigned short BRDV:2;
			unsigned short CPOL:1;
			unsigned short CPHA:1;
		} BIT;
	} SPCMD5;
	union {
		unsigned short WORD;
		struct {
			unsigned short SCKDEN:1;
			unsigned short SLNDEN:1;
			unsigned short SPNDEN:1;
			unsigned short LSBF:1;
			unsigned short SPB:4;
			unsigned short SSLKP:1;
			unsigned short SSLA:3;
			unsigned short BRDV:2;
			unsigned short CPOL:1;
			unsigned short CPHA:1;
		} BIT;
	} SPCMD6;
	union {
		unsigned short WORD;
		struct {
			unsigned short SCKDEN:1;
			unsigned short SLNDEN:1;
			unsigned short SPNDEN:1;
			unsigned short LSBF:1;
			unsigned short SPB:4;
			unsigned short SSLKP:1;
			unsigned short SSLA:3;
			unsigned short BRDV:2;
			unsigned short CPOL:1;
			unsigned short CPHA:1;
		} BIT;
	} SPCMD7;
};

struct st_rtc {
	union {
		unsigned char BYTE;
		struct {
			unsigned char F64HZ:1;
			unsigned char F32HZ:1;
			unsigned char F16HZ:1;
			unsigned char F8HZ:1;
			unsigned char F4HZ:1;
			unsigned char F2HZ:1;
			unsigned char F1HZ:1;
		} BIT;
	} R64CNT;
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char SEC10:3;
			unsigned char SEC1:4;
		} BIT;
	} RSECCNT;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char MIN10:3;
			unsigned char MIN1:4;
		} BIT;
	} RMINCNT;
	char           wk2[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char HOUR10:2;
			unsigned char HOUR1:4;
		} BIT;
	} RHRCNT;
	char           wk3[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char DAY:3;
		} BIT;
	} RWKCNT;
	char           wk4[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char DAY10:2;
			unsigned char DAY1:4;
		} BIT;
	} RDAYCNT;
	char           wk5[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char MON10:1;
			unsigned char MON1:4;
		} BIT;
	} RMONCNT;
	char           wk6[1];
	union {
		unsigned short WORD;
		struct {
			unsigned short YEAR1000:4;
			unsigned short YEAR100:4;
			unsigned short YEAR10:4;
			unsigned short YEAR1:4;
		} BIT;
	} RYRCNT;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ENB:1;
			unsigned char SEC10:3;
			unsigned char SEC1:4;
		} BIT;
	} RSECAR;
	char           wk7[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char ENB:1;
			unsigned char MIN10:3;
			unsigned char MIN1:4;
		} BIT;
	} RMINAR;
	char           wk8[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char ENB:1;
			unsigned char :1;
			unsigned char HOUR10:2;
			unsigned char HOUR1:4;
		} BIT;
	} RHRAR;
	char           wk9[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char ENB:1;
			unsigned char :4;
			unsigned char DAY:3;
		} BIT;
	} RWKAR;
	char           wk10[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char ENB:1;
			unsigned char :1;
			unsigned char DAY10:2;
			unsigned char DAY1:4;
		} BIT;
	} RDAYAR;
	char           wk11[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char ENB:1;
			unsigned char :2;
			unsigned char MON10:1;
			unsigned char MON1:4;
		} BIT;
	} RMONAR;
	char           wk12[1];
	union {
		unsigned short WORD;
		struct {
			unsigned short YEAR1000:4;
			unsigned short YEAR100:4;
			unsigned short YEAR10:4;
			unsigned short YEAR1:4;
		} BIT;
	} RYRAR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ENB:1;
		} BIT;
	} RYRAREN;
	char           wk13[3];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char PES:3;
			unsigned char :1;
			unsigned char PIE:1;
			unsigned char CIE:1;
			unsigned char AIE:1;
		} BIT;
	} RCR1;
	char           wk14[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char RTCOE:1;
			unsigned char ADJ:1;
			unsigned char RESET:1;
			unsigned char START:1;
		} BIT;
	} RCR2;
};

struct st_s12ad {
	union {
		unsigned char BYTE;
		struct {
			unsigned char ADST:1;
			unsigned char ADCS:1;
			unsigned char :1;
			unsigned char ADIE:1;
			unsigned char CKS:2;
			unsigned char TRGE:1;
			unsigned char EXTRG:1;
		} BIT;
	} ADCSR;
	char           wk0[3];
	union {
		unsigned short WORD;
		struct {
			unsigned short :8;
			unsigned short ANS:8;
		} BIT;
	} ADANS;
	char           wk1[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short :8;
			unsigned short ADS:8;
		} BIT;
	} ADADS;
	char           wk2[2];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char ADC:2;
		} BIT;
	} ADADC;
	char           wk3[1];
	union {
		unsigned short WORD;
		struct {
			unsigned short ADRFMT:1;
			unsigned short :9;
			unsigned short ACE:1;
		} BIT;
	} ADCER;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char ADSTRS:4;
		} BIT;
	} ADSTRGR;
	char           wk4[15];
	unsigned short ADDR0;
	unsigned short ADDR1;
	unsigned short ADDR2;
	unsigned short ADDR3;
	unsigned short ADDR4;
	unsigned short ADDR5;
	unsigned short ADDR6;
	unsigned short ADDR7;
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
			unsigned char MP:1;
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
			unsigned char MPIE:1;
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
			unsigned char MPB:1;
			unsigned char MPBT:1;
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
			unsigned long :1;
			unsigned long MSTPA29:1;
			unsigned long MSTPA28:1;
			unsigned long :4;
			unsigned long MSTPA23:1;
			unsigned long MSTPA22:1;
			unsigned long :2;
			unsigned long MSTPA19:1;
			unsigned long :1;
			unsigned long MSTPA17:1;
			unsigned long :1;
			unsigned long MSTPA15:1;
			unsigned long MSTPA14:1;
			unsigned long :2;
			unsigned long MSTPA11:1;
			unsigned long MSTPA10:1;
			unsigned long MSTPA9:1;
			unsigned long MSTPA8:1;
			unsigned long :2;
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
			unsigned long :1;
			unsigned long MSTPB26:1;
			unsigned long MSTPB25:1;
			unsigned long :1;
			unsigned long MSTPB23:1;
			unsigned long :1;
			unsigned long MSTPB21:1;
			unsigned long MSTPB20:1;
			unsigned long MSTPB19:1;
			unsigned long MSTPB18:1;
			unsigned long MSTPB17:1;
			unsigned long MSTPB16:1;
			unsigned long MSTPB15:1;
			unsigned long :14;
			unsigned long MSTPB0:1;
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
			unsigned long PSTOP0:1;
			unsigned long :2;
			unsigned long BCK:4;
			unsigned long :4;
			unsigned long PCK:4;
		} BIT;
	} SCKCR;
	char           wk4[12];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char BCLKDIV:1;
		} BIT;
	} BCKCR;
	char           wk5[15];
	union {
		unsigned short WORD;
		struct {
			unsigned short KEY:8;
			unsigned short OSTDE:1;
			unsigned short OSTDF:1;
		} BIT;
	} OSTDCR;
	char           wk6[49726];
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
			unsigned char DUSBE:1;
			unsigned char DRTCE:1;
			unsigned char DLVDE:1;
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
			unsigned char DUSBF:1;
			unsigned char DRTCFF:1;
			unsigned char DLVDF:1;
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
			unsigned char :4;
			unsigned char LVD2F:1;
			unsigned char LVD1F:1;
			unsigned char PORF:1;
		} BIT;
	} RSTSR;
	char           wk7[4];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char SUBSTOP:1;
		} BIT;
	} SUBOSCCR;
	char           wk8[1];
	unsigned char  LVDKEYR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char LVD2E:1;
			unsigned char LVD2RI:1;
			unsigned char :2;
			unsigned char LVD1E:1;
			unsigned char LVD1RI:1;
		} BIT;
	} LVDCR;
	char           wk9[2];
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

struct st_usb {
	union {
		unsigned long LONG;
		struct {
			unsigned long DVSTS1:1;
			unsigned long :1;
			unsigned long DOVCB1:1;
			unsigned long DOVCA1:1;
			unsigned long :2;
			unsigned long DM1:1;
			unsigned long DP1:1;
			unsigned long DVBSTS0:1;
			unsigned long :1;
			unsigned long DOVCB0:1;
			unsigned long DOVCA0:1;
			unsigned long :2;
			unsigned long DM0:1;
			unsigned long DP0:1;
			unsigned long :3;
			unsigned long FIXPHY1:1;
			unsigned long :3;
			unsigned long SRPC1:1;
			unsigned long :3;
			unsigned long FIXPHY0:1;
			unsigned long :3;
			unsigned long SRPC0:1;
		} BIT;
	} DPUSR0R;
	union {
		unsigned long LONG;
		struct {
			unsigned long DVBINT1:1;
			unsigned long :1;
			unsigned long DOVRCRB1:1;
			unsigned long DOVRCRA1:1;
			unsigned long :2;
			unsigned long DMINT1:1;
			unsigned long DPINT1:1;
			unsigned long DVBINT0:1;
			unsigned long :1;
			unsigned long DOVRCRB0:1;
			unsigned long DOVRCRA0:1;
			unsigned long :2;
			unsigned long DMINT0:1;
			unsigned long DPINT0:1;
			unsigned long DVBSE1:1;
			unsigned long :1;
			unsigned long DOVRCRBE1:1;
			unsigned long DOVRCRAE1:1;
			unsigned long :2;
			unsigned long DMINTE1:1;
			unsigned long DPINTE1:1;
			unsigned long DVBSE0:1;
			unsigned long :1;
			unsigned long DOVRCRBE0:1;
			unsigned long DOVRCRAE0:1;
			unsigned long :2;
			unsigned long DMINTE0:1;
			unsigned long DPINTE0:1;
		} BIT;
	} DPUSR1R;
};

struct st_usb0 {
	union {
		unsigned short WORD;
		struct {
			unsigned short :5;
			unsigned short SCKE:1;
			unsigned short :3;
			unsigned short DCFM:1;
			unsigned short DRPD:1;
			unsigned short DPRPU:1;
			unsigned short :3;
			unsigned short USBE:1;
		} BIT;
	} SYSCFG;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short OVCMON:2;
			unsigned short :7;
			unsigned short HTACT:1;
			unsigned short :3;
			unsigned short IDMON:1;
			unsigned short LNST:2;
		} BIT;
	} SYSSTS0;
	char           wk1[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short HNPBTOA:1;
			unsigned short EXICEN:1;
			unsigned short VBUSEN:1;
			unsigned short WKUP:1;
			unsigned short RWUPE:1;
			unsigned short USBRST:1;
			unsigned short RESUME:1;
			unsigned short UACT:1;
			unsigned short :1;
			unsigned short RHST:3;
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
			unsigned short RCNT:1;
			unsigned short REW:1;
			unsigned short :3;
			unsigned short MBW:1;
			unsigned short :1;
			unsigned short BIGEND:1;
			unsigned short :2;
			unsigned short ISEL:1;
			unsigned short :1;
			unsigned short CURPIPE:4;
		} BIT;
	} CFIFOSEL;
	union {
		unsigned short WORD;
		struct {
			unsigned short BVAL:1;
			unsigned short BCLR:1;
			unsigned short FRDY:1;
			unsigned short :4;
			unsigned short DTLN:9;
		} BIT;
	} CFIFOCTR;
	char           wk6[4];
	union {
		unsigned short WORD;
		struct {
			unsigned short RCNT:1;
			unsigned short REW:1;
			unsigned short DCLRM:1;
			unsigned short DREQE:1;
			unsigned short :1;
			unsigned short MBW:1;
			unsigned short :1;
			unsigned short BIGEND:1;
			unsigned short :4;
			unsigned short CURPIPE:4;
		} BIT;
	} D0FIFOSEL;
	union {
		unsigned short WORD;
		struct {
			unsigned short BVAL:1;
			unsigned short BCLR:1;
			unsigned short FRDY:1;
			unsigned short :4;
			unsigned short DTLN:9;
		} BIT;
	} D0FIFOCTR;
	union {
		unsigned short WORD;
		struct {
			unsigned short RCNT:1;
			unsigned short REW:1;
			unsigned short DCLRM:1;
			unsigned short DREQE:1;
			unsigned short :1;
			unsigned short MBW:1;
			unsigned short :1;
			unsigned short BIGEND:1;
			unsigned short :4;
			unsigned short CURPIPE:4;
		} BIT;
	} D1FIFOSEL;
	union {
		unsigned short WORD;
		struct {
			unsigned short BVAL:1;
			unsigned short BCLR:1;
			unsigned short FRDY:1;
			unsigned short :4;
			unsigned short DTLN:9;
		} BIT;
	} D1FIFOCTR;
	union {
		unsigned short WORD;
		struct {
			unsigned short VBSE:1;
			unsigned short RSME:1;
			unsigned short SOFE:1;
			unsigned short DVSE:1;
			unsigned short CTRE:1;
			unsigned short BEMPE:1;
			unsigned short NRDYE:1;
			unsigned short BRDYE:1;
		} BIT;
	} INTENB0;
	union {
		unsigned short WORD;
		struct {
			unsigned short OVRCRE:1;
			unsigned short BCHGE:1;
			unsigned short :1;
			unsigned short DTCHE:1;
			unsigned short ATTCHE:1;
			unsigned short :4;
			unsigned short EOFERRE:1;
			unsigned short SIGNE:1;
			unsigned short SACKE:1;
		} BIT;
	} INTENB1;
	char           wk7[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short :6;
			unsigned short PIPE9BRDYE:1;
			unsigned short PIPE8BRDYE:1;
			unsigned short PIPE7BRDYE:1;
			unsigned short PIPE6BRDYE:1;
			unsigned short PIPE5BRDYE:1;
			unsigned short PIPE4BRDYE:1;
			unsigned short PIPE3BRDYE:1;
			unsigned short PIPE2BRDYE:1;
			unsigned short PIPE1BRDYE:1;
			unsigned short PIPE0BRDYE:1;
		} BIT;
	} BRDYENB;
	union {
		unsigned short WORD;
		struct {
			unsigned short :6;
			unsigned short PIPE9BRDYE:1;
			unsigned short PIPE8BRDYE:1;
			unsigned short PIPE7BRDYE:1;
			unsigned short PIPE6BRDYE:1;
			unsigned short PIPE5BRDYE:1;
			unsigned short PIPE4BRDYE:1;
			unsigned short PIPE3BRDYE:1;
			unsigned short PIPE2BRDYE:1;
			unsigned short PIPE1BRDYE:1;
			unsigned short PIPE0BRDYE:1;
		} BIT;
	} NRDYENB;
	union {
		unsigned short WORD;
		struct {
			unsigned short :6;
			unsigned short PIPE9BEMPE:1;
			unsigned short PIPE8BEMPE:1;
			unsigned short PIPE7BEMPE:1;
			unsigned short PIPE6BEMPE:1;
			unsigned short PIPE5BEMPE:1;
			unsigned short PIPE4BEMPE:1;
			unsigned short PIPE3BEMPE:1;
			unsigned short PIPE2BEMPE:1;
			unsigned short PIPE1BEMPE:1;
			unsigned short PIPE0BEMPE:1;
		} BIT;
	} BEMPENB;
	union {
		unsigned short WORD;
		struct {
			unsigned short :7;
			unsigned short TRNENSEL:1;
			unsigned short :1;
			unsigned short BRDYM:1;
			unsigned short :1;
			unsigned short EDGESTS:1;
		} BIT;
	} SOFCFG;
	char           wk8[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short VBINT:1;
			unsigned short RESM:1;
			unsigned short SOFR:1;
			unsigned short DVST:1;
			unsigned short CTRT:1;
			unsigned short BEMP:1;
			unsigned short NRDY:1;
			unsigned short BRDY:1;
			unsigned short VBSTS:1;
			unsigned short DVSQ:3;
			unsigned short VALID:1;
			unsigned short CTSQ:3;
		} BIT;
	} INTSTS0;
	union {
		unsigned short WORD;
		struct {
			unsigned short OVRCR:1;
			unsigned short BCHG:1;
			unsigned short :1;
			unsigned short DTCH:1;
			unsigned short ATTCH:1;
			unsigned short :4;
			unsigned short EOFERR:1;
			unsigned short SIGN:1;
			unsigned short SACK:1;
		} BIT;
	} INTSTS1;
	char           wk9[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short :6;
			unsigned short PIPE9BRDY:1;
			unsigned short PIPE8BRDY:1;
			unsigned short PIPE7BRDY:1;
			unsigned short PIPE6BRDY:1;
			unsigned short PIPE5BRDY:1;
			unsigned short PIPE4BRDY:1;
			unsigned short PIPE3BRDY:1;
			unsigned short PIPE2BRDY:1;
			unsigned short PIPE1BRDY:1;
			unsigned short PIPE0BRDY:1;
		} BIT;
	} BRDYSTS;
	union {
		unsigned short WORD;
		struct {
			unsigned short :6;
			unsigned short PIPE9BRDY:1;
			unsigned short PIPE8BRDY:1;
			unsigned short PIPE7BRDY:1;
			unsigned short PIPE6BRDY:1;
			unsigned short PIPE5BRDY:1;
			unsigned short PIPE4BRDY:1;
			unsigned short PIPE3BRDY:1;
			unsigned short PIPE2BRDY:1;
			unsigned short PIPE1BRDY:1;
			unsigned short PIPE0BRDY:1;
		} BIT;
	} NRDYSTS;
	union {
		unsigned short WORD;
		struct {
			unsigned short :6;
			unsigned short PIPE9BENP:1;
			unsigned short PIPE8BENP:1;
			unsigned short PIPE7BENP:1;
			unsigned short PIPE6BENP:1;
			unsigned short PIPE5BENP:1;
			unsigned short PIPE4BENP:1;
			unsigned short PIPE3BENP:1;
			unsigned short PIPE2BENP:1;
			unsigned short PIPE1BENP:1;
			unsigned short PIPE0BENP:1;
		} BIT;
	} BEMPSTS;
	union {
		unsigned short WORD;
		struct {
			unsigned short OVRN:1;
			unsigned short CRCE:1;
			unsigned short :3;
			unsigned short FRNM:11;
		} BIT;
	} FRMNUM;
	union {
		unsigned short WORD;
		struct {
			unsigned short DVCHG:1;
		} BIT;
	} DVCHGR;
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short STSRECOV:4;
			unsigned short :1;
			unsigned short USBADDR:7;
		} BIT;
	} USBADDR;
	char           wk10[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short BREQUEST:8;
			unsigned short BMREQUESTTYPE:8;
		} BIT;
	} USBREQ;
	unsigned short USBVAL;
	unsigned short USBINDX;
	unsigned short USBLENG;
	union {
		unsigned short WORD;
		struct {
			unsigned short :8;
			unsigned short SHTNAK:1;
			unsigned short :2;
			unsigned short DIR:1;
		} BIT;
	} DCPCFG;
	union {
		unsigned short WORD;
		struct {
			unsigned short DEVSEL:4;
			unsigned short :5;
			unsigned short MXPS:7;
		} BIT;
	} DCPMAXP;
	union {
		unsigned short WORD;
		struct {
			unsigned short BSTS:1;
			unsigned short SUREQ:1;
			unsigned short :2;
			unsigned short SUREQCLR:1;
			unsigned short :2;
			unsigned short SQCLR:1;
			unsigned short SQSET:1;
			unsigned short SQMON:1;
			unsigned short PBUSY:1;
			unsigned short :2;
			unsigned short CCPL:1;
			unsigned short PID:2;
		} BIT;
	} DCPCTR;
	char           wk11[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short :12;
			unsigned short PIPESEL:4;
		} BIT;
	} PIPESEL;
	char           wk12[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short TYPE:2;
			unsigned short :3;
			unsigned short BFRE:1;
			unsigned short DBLB:1;
			unsigned short :1;
			unsigned short SHTNAK:1;
			unsigned short :2;
			unsigned short DIR:1;
			unsigned short EPNUM:4;
		} BIT;
	} PIPECFG;
	char           wk13[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short DEVSEL:4;
			unsigned short :3;
			unsigned short MXPS:9;
		} BIT;
	} PIPEMAXP;
	union {
		unsigned short WORD;
		struct {
			unsigned short :3;
			unsigned short IFIS:1;
			unsigned short :9;
			unsigned short IITV:3;
		} BIT;
	} PIPEPERI;
	union {
		unsigned short WORD;
		struct {
			unsigned short BSTS:1;
			unsigned short INBUFM:1;
			unsigned short :3;
			unsigned short ATREPM:1;
			unsigned short ACLRM:1;
			unsigned short SQCLR:1;
			unsigned short SQSET:1;
			unsigned short SQMON:1;
			unsigned short PBUSY:1;
			unsigned short :3;
			unsigned short PID:2;
		} BIT;
	} PIPE1CTR;
	union {
		unsigned short WORD;
		struct {
			unsigned short BSTS:1;
			unsigned short INBUFM:1;
			unsigned short :3;
			unsigned short ATREPM:1;
			unsigned short ACLRM:1;
			unsigned short SQCLR:1;
			unsigned short SQSET:1;
			unsigned short SQMON:1;
			unsigned short PBUSY:1;
			unsigned short :3;
			unsigned short PID:2;
		} BIT;
	} PIPE2CTR;
	union {
		unsigned short WORD;
		struct {
			unsigned short BSTS:1;
			unsigned short INBUFM:1;
			unsigned short :3;
			unsigned short ATREPM:1;
			unsigned short ACLRM:1;
			unsigned short SQCLR:1;
			unsigned short SQSET:1;
			unsigned short SQMON:1;
			unsigned short PBUSY:1;
			unsigned short :3;
			unsigned short PID:2;
		} BIT;
	} PIPE3CTR;
	union {
		unsigned short WORD;
		struct {
			unsigned short BSTS:1;
			unsigned short INBUFM:1;
			unsigned short :3;
			unsigned short ATREPM:1;
			unsigned short ACLRM:1;
			unsigned short SQCLR:1;
			unsigned short SQSET:1;
			unsigned short SQMON:1;
			unsigned short PBUSY:1;
			unsigned short :3;
			unsigned short PID:2;
		} BIT;
	} PIPE4CTR;
	union {
		unsigned short WORD;
		struct {
			unsigned short BSTS:1;
			unsigned short INBUFM:1;
			unsigned short :3;
			unsigned short ATREPM:1;
			unsigned short ACLRM:1;
			unsigned short SQCLR:1;
			unsigned short SQSET:1;
			unsigned short SQMON:1;
			unsigned short PBUSY:1;
			unsigned short :3;
			unsigned short PID:2;
		} BIT;
	} PIPE5CTR;
	union {
		unsigned short WORD;
		struct {
			unsigned short BSTS:1;
			unsigned short :5;
			unsigned short ACLRM:1;
			unsigned short SQCLR:1;
			unsigned short SQSET:1;
			unsigned short SQMON:1;
			unsigned short PBUSY:1;
			unsigned short :3;
			unsigned short PID:2;
		} BIT;
	} PIPE6CTR;
	union {
		unsigned short WORD;
		struct {
			unsigned short BSTS:1;
			unsigned short :5;
			unsigned short ACLRM:1;
			unsigned short SQCLR:1;
			unsigned short SQSET:1;
			unsigned short SQMON:1;
			unsigned short PBUSY:1;
			unsigned short :3;
			unsigned short PID:2;
		} BIT;
	} PIPE7CTR;
	union {
		unsigned short WORD;
		struct {
			unsigned short BSTS:1;
			unsigned short :5;
			unsigned short ACLRM:1;
			unsigned short SQCLR:1;
			unsigned short SQSET:1;
			unsigned short SQMON:1;
			unsigned short PBUSY:1;
			unsigned short :3;
			unsigned short PID:2;
		} BIT;
	} PIPE8CTR;
	union {
		unsigned short WORD;
		struct {
			unsigned short BSTS:1;
			unsigned short :5;
			unsigned short ACLRM:1;
			unsigned short SQCLR:1;
			unsigned short SQSET:1;
			unsigned short SQMON:1;
			unsigned short PBUSY:1;
			unsigned short :3;
			unsigned short PID:2;
		} BIT;
	} PIPE9CTR;
	char           wk14[14];
	union {
		unsigned short WORD;
		struct {
			unsigned short :6;
			unsigned short TRENB:1;
			unsigned short TRCLR:1;
		} BIT;
	} PIPE1TRE;
	unsigned short PIPE1TRN;
	union {
		unsigned short WORD;
		struct {
			unsigned short :6;
			unsigned short TRENB:1;
			unsigned short TRCLR:1;
		} BIT;
	} PIPE2TRE;
	unsigned short PIPE2TRN;
	union {
		unsigned short WORD;
		struct {
			unsigned short :6;
			unsigned short TRENB:1;
			unsigned short TRCLR:1;
		} BIT;
	} PIPE3TRE;
	unsigned short PIPE3TRN;
	union {
		unsigned short WORD;
		struct {
			unsigned short :6;
			unsigned short TRENB:1;
			unsigned short TRCLR:1;
		} BIT;
	} PIPE4TRE;
	unsigned short PIPE4TRN;
	union {
		unsigned short WORD;
		struct {
			unsigned short :6;
			unsigned short TRENB:1;
			unsigned short TRCLR:1;
		} BIT;
	} PIPE5TRE;
	unsigned short PIPE5TRN;
	char           wk15[44];
	union {
		unsigned short WORD;
		struct {
			unsigned short :8;
			unsigned short USBSPD:2;
		} BIT;
	} DEVADD0;
	union {
		unsigned short WORD;
		struct {
			unsigned short :8;
			unsigned short USBSPD:2;
		} BIT;
	} DEVADD1;
	union {
		unsigned short WORD;
		struct {
			unsigned short :8;
			unsigned short USBSPD:2;
		} BIT;
	} DEVADD2;
	union {
		unsigned short WORD;
		struct {
			unsigned short :8;
			unsigned short USBSPD:2;
		} BIT;
	} DEVADD3;
	union {
		unsigned short WORD;
		struct {
			unsigned short :8;
			unsigned short USBSPD:2;
		} BIT;
	} DEVADD4;
	union {
		unsigned short WORD;
		struct {
			unsigned short :8;
			unsigned short USBSPD:2;
		} BIT;
	} DEVADD5;
};

union un_wdt {
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
	struct {
		unsigned short WINA;
		unsigned short WINB;
	} WRITE;
};

enum enum_ir {
IR_BSC_BUSERR=16,IR_FCU_FIFERR=21,IR_FCU_FRDYI=23,
IR_ICU_SWINT=27,
IR_CMT0_CMI0,
IR_CMT1_CMI1,
IR_CMT2_CMI2,
IR_CMT3_CMI3,
IR_ETHER_EINT,
IR_USB0_D0FIFO0=36,IR_USB0_D1FIFO0,IR_USB0_USBI0,
IR_USB1_D0FIFO1=40,IR_USB1_D1FIFO1,IR_USB1_USBI1,
IR_RSPI0_SPEI0=44,IR_RSPI0_SPRI0,IR_RSPI0_SPTI0,IR_RSPI0_SPII0,
IR_RSPI1_SPEI1,IR_RSPI1_SPRI1,IR_RSPI1_SPTI1,IR_RSPI1_SPII1,
IR_CAN0_ERS0=56,IR_CAN0_RXF0,IR_CAN0_TXF0,IR_CAN0_RXM0,IR_CAN0_TXM0,
IR_RTC_PRD=62,IR_RTC_CUP,
IR_ICU_IRQ0,IR_ICU_IRQ1,IR_ICU_IRQ2,IR_ICU_IRQ3,IR_ICU_IRQ4,IR_ICU_IRQ5,IR_ICU_IRQ6,IR_ICU_IRQ7,IR_ICU_IRQ8,IR_ICU_IRQ9,IR_ICU_IRQ10,IR_ICU_IRQ11,IR_ICU_IRQ12,IR_ICU_IRQ13,IR_ICU_IRQ14,IR_ICU_IRQ15,
IR_USB_USBR0=90,IR_USB_USBR1,
IR_RTC_ALM,
IR_WDT_WOVI=96,
IR_AD0_ADI0=98,
IR_AD1_ADI1,
IR_S12AD_ADI=102,
IR_MTU0_TGIA0=114,IR_MTU0_TGIB0,IR_MTU0_TGIC0,IR_MTU0_TGID0,IR_MTU0_TCIV0,IR_MTU0_TGIE0,IR_MTU0_TGIF0,
IR_MTU1_TGIA1,IR_MTU1_TGIB1,IR_MTU1_TCIV1,IR_MTU1_TCIU1,
IR_MTU2_TGIA2,IR_MTU2_TGIB2,IR_MTU2_TCIV2,IR_MTU2_TCIU2,
IR_MTU3_TGIA3,IR_MTU3_TGIB3,IR_MTU3_TGIC3,IR_MTU3_TGID3,IR_MTU3_TCIV3,
IR_MTU4_TGIA4,IR_MTU4_TGIB4,IR_MTU4_TGIC4,IR_MTU4_TGID4,IR_MTU4_TCIV4,
IR_MTU5_TGIU5,IR_MTU5_TGIV5,IR_MTU5_TGIW5,
IR_MTU6_TGIA6,IR_MTU6_TGIB6,IR_MTU6_TGIC6,IR_MTU6_TGID6,IR_MTU6_TCIV6,IR_MTU6_TGIE6,IR_MTU6_TGIF6,
IR_MTU7_TGIA7,IR_MTU7_TGIB7,IR_MTU7_TCIV7,IR_MTU7_TCIU7,
IR_MTU8_TGIA8,IR_MTU8_TGIB8,IR_MTU8_TCIV8,IR_MTU8_TCIU8,
IR_MTU9_TGIA9,IR_MTU9_TGIB9,IR_MTU9_TGIC9,IR_MTU9_TGID9,IR_MTU9_TCIV9,
IR_MTU10_TGIA10,IR_MTU10_TGIB10,IR_MTU10_TGIC10,IR_MTU10_TGID10,IR_MTU10_TCIV10,
IR_MTU11_TGIU11,IR_MTU11_TGIV11,IR_MTU11_TGIW11,
IR_POE_OEI1,IR_POE_OEI2,IR_POE_OEI3,IR_POE_OEI4,
IR_TMR0_CMIA0,IR_TMR0_CMIB0,IR_TMR0_OVI0,
IR_TMR1_CMIA1,IR_TMR1_CMIB1,IR_TMR1_OVI1,
IR_TMR2_CMIA2,IR_TMR2_CMIB2,IR_TMR2_OVI2,
IR_TMR3_CMIA3,IR_TMR3_CMIB3,IR_TMR3_OVI3,
IR_DMAC_DMAC0I=198,IR_DMAC_DMAC1I,IR_DMAC_DMAC2I,IR_DMAC_DMAC3I,
IR_EXDMAC_EXDMAC0I,IR_EXDMAC_EXDMAC1I,
IR_SCI0_ERI0=214,IR_SCI0_RXI0,IR_SCI0_TXI0,IR_SCI0_TEI0,
IR_SCI1_ERI1,IR_SCI1_RXI1,IR_SCI1_TXI1,IR_SCI1_TEI1,
IR_SCI2_ERI2,IR_SCI2_RXI2,IR_SCI2_TXI2,IR_SCI2_TEI2,
IR_SCI3_ERI3,IR_SCI3_RXI3,IR_SCI3_TXI3,IR_SCI3_TEI3,
IR_SCI5_ERI5=234,IR_SCI5_RXI5,IR_SCI5_TXI5,IR_SCI5_TEI5,
IR_SCI6_ERI6,IR_SCI6_RXI6,IR_SCI6_TXI6,IR_SCI6_TEI6,
IR_RIIC0_ICEEI0=246,IR_RIIC0_ICRXI0,IR_RIIC0_ICTXI0,IR_RIIC0_ICTEI0,
IR_RIIC1_ICEEI1,IR_RIIC1_ICRXI1,IR_RIIC1_ICTXI1,IR_RIIC1_ICTEI1
};

enum enum_dtce {
DTCE_ICU_SWINT=27,
DTCE_CMT0_CMI0,
DTCE_CMT1_CMI1,
DTCE_CMT2_CMI2,
DTCE_CMT3_CMI3,
DTCE_USB0_D0FIFO0=36,DTCE_USB0_D1FIFO0,
DTCE_USB1_D0FIFO1=40,DTCE_USB1_D1FIFO1,
DTCE_RSPI0_SPRI0=45,DTCE_RSPI0_SPTI0,
DTCE_RSPI1_SPRI1=49,DTCE_RSPI1_SPTI1,
DTCE_ICU_IRQ0=64,DTCE_ICU_IRQ1,DTCE_ICU_IRQ2,DTCE_ICU_IRQ3,DTCE_ICU_IRQ4,DTCE_ICU_IRQ5,DTCE_ICU_IRQ6,DTCE_ICU_IRQ7,DTCE_ICU_IRQ8,DTCE_ICU_IRQ9,DTCE_ICU_IRQ10,DTCE_ICU_IRQ11,DTCE_ICU_IRQ12,DTCE_ICU_IRQ13,DTCE_ICU_IRQ14,DTCE_ICU_IRQ15,
DTCE_AD0_ADI0=98,
DTCE_AD1_ADI1,
DTCE_S12AD_ADI=102,
DTCE_MTU0_TGIA0=114,DTCE_MTU0_TGIB0,DTCE_MTU0_TGIC0,DTCE_MTU0_TGID0,
DTCE_MTU1_TGIA1=121,DTCE_MTU1_TGIB1,
DTCE_MTU2_TGIA2=125,DTCE_MTU2_TGIB2,
DTCE_MTU3_TGIA3=129,DTCE_MTU3_TGIB3,DTCE_MTU3_TGIC3,DTCE_MTU3_TGID3,
DTCE_MTU4_TGIA4=134,DTCE_MTU4_TGIB4,DTCE_MTU4_TGIC4,DTCE_MTU4_TGID4,DTCE_MTU4_TCIV4,
DTCE_MTU5_TGIU5,DTCE_MTU5_TGIV5,DTCE_MTU5_TGIW5,
DTCE_MTU6_TGIA6,DTCE_MTU6_TGIB6,DTCE_MTU6_TGIC6,DTCE_MTU6_TGID6,
DTCE_MTU7_TGIA7=149,DTCE_MTU7_TGIB7,
DTCE_MTU8_TGIA8=153,DTCE_MTU8_TGIB8,
DTCE_MTU9_TGIA9=157,DTCE_MTU9_TGIB9,DTCE_MTU9_TGIC9,DTCE_MTU9_TGID9,
DTCE_MTU10_TGIA10=162,DTCE_MTU10_TGIB10,DTCE_MTU10_TGIC10,DTCE_MTU10_TGID10,DTCE_MTU10_TCIV10,
DTCE_MTU11_TGIU11,DTCE_MTU11_TGIV11,DTCE_MTU11_TGIW11,
DTCE_TMR0_CMIA0=174,DTCE_TMR0_CMIB0,
DTCE_TMR1_CMIA1=177,DTCE_TMR1_CMIB1,
DTCE_TMR2_CMIA2=180,DTCE_TMR2_CMIB2,
DTCE_TMR3_CMIA3=183,DTCE_TMR3_CMIB3,
DTCE_DMAC_DMAC0I=198,DTCE_DMAC_DMAC1I,DTCE_DMAC_DMAC2I,DTCE_DMAC_DMAC3I,
DTCE_EXDMAC_EXDMAC0I,DTCE_EXDMAC_EXDMAC1I,
DTCE_SCI0_RXI0=215,DTCE_SCI0_TXI0,
DTCE_SCI1_RXI1=219,DTCE_SCI1_TXI1,
DTCE_SCI2_RXI2=223,DTCE_SCI2_TXI2,
DTCE_SCI3_RXI3=227,DTCE_SCI3_TXI3,
DTCE_SCI5_RXI5=235,DTCE_SCI5_TXI5,
DTCE_SCI6_RXI6=239,DTCE_SCI6_TXI6,
DTCE_RIIC0_ICRXI0=247,DTCE_RIIC0_ICTXI0,
DTCE_RIIC1_ICRXI1=251,DTCE_RIIC1_ICTXI1
};

enum enum_ier {
IER_BSC_BUSERR=0x02,
IER_FCU_FIFERR=0x02,IER_FCU_FRDYI=0x02,
IER_ICU_SWINT=0x03,
IER_CMT0_CMI0=0x03,
IER_CMT1_CMI1=0x03,
IER_CMT2_CMI2=0x03,
IER_CMT3_CMI3=0x03,
IER_ETHER_EINT=0x04,
IER_USB0_D0FIFO0=0x04,IER_USB0_D1FIFO0=0x04,IER_USB0_USBI0=0x04,
IER_USB1_D0FIFO1=0x05,IER_USB1_D1FIFO1=0x05,IER_USB1_USBI1=0x05,
IER_RSPI0_SPEI0=0x05,IER_RSPI0_SPRI0=0x05,IER_RSPI0_SPTI0=0x05,IER_RSPI0_SPII0=0x05,
IER_RSPI1_SPEI1=0x06,IER_RSPI1_SPRI1=0x06,IER_RSPI1_SPTI1=0x06,IER_RSPI1_SPII1=0x06,
IER_CAN0_ERS0=0x07,IER_CAN0_RXF0=0x07,IER_CAN0_TXF0=0x07,IER_CAN0_RXM0=0x07,IER_CAN0_TXM0=0x07,
IER_RTC_PRD=0x07,IER_RTC_CUP=0x07,
IER_ICU_IRQ0=0x08,IER_ICU_IRQ1=0x08,IER_ICU_IRQ2=0x08,IER_ICU_IRQ3=0x08,IER_ICU_IRQ4=0x08,IER_ICU_IRQ5=0x08,IER_ICU_IRQ6=0x08,IER_ICU_IRQ7=0x08,IER_ICU_IRQ8=0x09,IER_ICU_IRQ9=0x09,IER_ICU_IRQ10=0x09,IER_ICU_IRQ11=0x09,IER_ICU_IRQ12=0x09,IER_ICU_IRQ13=0x09,IER_ICU_IRQ14=0x09,IER_ICU_IRQ15=0x09,
IER_USB_USBR0=0x0B,IER_USB_USBR1=0x0B,
IER_RTC_ALM=0x0B,
IER_WDT_WOVI=0x0C,
IER_AD0_ADI0=0x0C,
IER_AD1_ADI1=0x0C,
IER_S12AD_ADI=0x0C,
IER_MTU0_TGIA0=0x0E,IER_MTU0_TGIB0=0x0E,IER_MTU0_TGIC0=0x0E,IER_MTU0_TGID0=0x0E,IER_MTU0_TCIV0=0x0E,IER_MTU0_TGIE0=0x0E,IER_MTU0_TGIF0=0x0F,
IER_MTU1_TGIA1=0x0F,IER_MTU1_TGIB1=0x0F,IER_MTU1_TCIV1=0x0F,IER_MTU1_TCIU1=0x0F,
IER_MTU2_TGIA2=0x0F,IER_MTU2_TGIB2=0x0F,IER_MTU2_TCIV2=0x0F,IER_MTU2_TCIU2=0x10,
IER_MTU3_TGIA3=0x10,IER_MTU3_TGIB3=0x10,IER_MTU3_TGIC3=0x10,IER_MTU3_TGID3=0x10,IER_MTU3_TCIV3=0x10,
IER_MTU4_TGIA4=0x10,IER_MTU4_TGIB4=0x10,IER_MTU4_TGIC4=0x11,IER_MTU4_TGID4=0x11,IER_MTU4_TCIV4=0x11,
IER_MTU5_TGIU5=0x11,IER_MTU5_TGIV5=0x11,IER_MTU5_TGIW5=0x10,
IER_MTU6_TGIA6=0x11,IER_MTU6_TGIB6=0x11,IER_MTU6_TGIC6=0x12,IER_MTU6_TGID6=0x12,IER_MTU6_TCIV6=0x12,IER_MTU6_TGIE6=0x12,IER_MTU6_TGIF6=0x12,
IER_MTU7_TGIA7=0x12,IER_MTU7_TGIB7=0x12,IER_MTU7_TCIV7=0x12,IER_MTU7_TCIU7=0x13,
IER_MTU8_TGIA8=0x13,IER_MTU8_TGIB8=0x13,IER_MTU8_TCIV8=0x13,IER_MTU8_TCIU8=0x13,
IER_MTU9_TGIA9=0x13,IER_MTU9_TGIB9=0x13,IER_MTU9_TGIC9=0x13,IER_MTU9_TGID9=0x14,IER_MTU9_TCIV9=0x14,
IER_MTU10_TGIA10=0x14,IER_MTU10_TGIB10=0x14,IER_MTU10_TGIC10=0x14,IER_MTU10_TGID10=0x14,IER_MTU10_TCIV10=0x14,
IER_MTU11_TGIU11=0x14,IER_MTU11_TGIV11=0x15,IER_MTU11_TGIW11=0x15,
IER_POE_OEI1=0x15,IER_POE_OEI2=0x15,IER_POE_OEI3=0x15,IER_POE_OEI4=0x15,
IER_TMR0_CMIA0=0x15,IER_TMR0_CMIB0=0x15,IER_TMR0_OVI0=0x16,
IER_TMR1_CMIA1=0x16,IER_TMR1_CMIB1=0x16,IER_TMR1_OVI1=0x16,
IER_TMR2_CMIA2=0x16,IER_TMR2_CMIB2=0x16,IER_TMR2_OVI2=0x16,
IER_TMR3_CMIA3=0x16,IER_TMR3_CMIB3=0x17,IER_TMR3_OVI3=0x17,
IER_DMAC_DMAC0I=0x18,IER_DMAC_DMAC1I=0x18,IER_DMAC_DMAC2I=0x19,IER_DMAC_DMAC3I=0x19,
IER_EXDMAC_EXDMAC0I=0x19,IER_EXDMAC_EXDMAC1I=0x19,
IER_SCI0_ERI0=0x1A,IER_SCI0_RXI0=0x1A,IER_SCI0_TXI0=0x1B,IER_SCI0_TEI0=0x1B,
IER_SCI1_ERI1=0x1B,IER_SCI1_RXI1=0x1B,IER_SCI1_TXI1=0x1B,IER_SCI1_TEI1=0x1B,
IER_SCI2_ERI2=0x1B,IER_SCI2_RXI2=0x1B,IER_SCI2_TXI2=0x1C,IER_SCI2_TEI2=0x1C,
IER_SCI3_ERI3=0x1C,IER_SCI3_RXI3=0x1C,IER_SCI3_TXI3=0x1C,IER_SCI3_TEI3=0x1C,
IER_SCI5_ERI5=0x1D,IER_SCI5_RXI5=0x1D,IER_SCI5_TXI5=0x1D,IER_SCI5_TEI5=0x1D,
IER_SCI6_ERI6=0x1D,IER_SCI6_RXI6=0x1D,IER_SCI6_TXI6=0x1E,IER_SCI6_TEI6=0x1E,
IER_RIIC0_ICEEI0=0x1E,IER_RIIC0_ICRXI0=0x1E,IER_RIIC0_ICTXI0=0x1F,IER_RIIC0_ICTEI0=0x1F,
IER_RIIC1_ICEEI1=0x1F,IER_RIIC1_ICRXI1=0x1F,IER_RIIC1_ICTXI1=0x1F,IER_RIIC1_ICTEI1=0x1F
};

enum enum_ipr {
IPR_BSC_BUSERR=0x00,
IPR_FCU_FIFERR=0x01,IPR_FCU_FRDYI=0x02,
IPR_ICU_SWINT=0x03,
IPR_CMT0_CMI0=0x04,
IPR_CMT1_CMI1=0x05,
IPR_CMT2_CMI2=0x06,
IPR_CMT3_CMI3=0x07,
IPR_ETHER_EINT=0x08,
IPR_USB0_D0FIFO0=0x0C,IPR_USB0_D1FIFO0=0x0D,IPR_USB0_USBI0=0x0E,
IPR_USB1_D0FIFO1=0x10,IPR_USB1_D1FIFO1=0x11,IPR_USB1_USBI1=0x12,
IPR_RSPI0_SPEI0=0x14,IPR_RSPI0_SPRI0=0x14,IPR_RSPI0_SPTI0=0x14,IPR_RSPI0_SPII0=0x14,
IPR_RSPI1_SPEI1=0x15,IPR_RSPI1_SPRI1=0x15,IPR_RSPI1_SPTI1=0x15,IPR_RSPI1_SPII1=0x15,
IPR_CAN0_ERS0=0x18,IPR_CAN0_RXF0=0x18,IPR_CAN0_TXF0=0x18,IPR_CAN0_RXM0=0x18,IPR_CAN0_TXM0=0x18,
IPR_RTC_PRD=0x1E,IPR_RTC_CUP=0x1F,
IPR_ICU_IRQ0=0x20,IPR_ICU_IRQ1=0x21,IPR_ICU_IRQ2=0x22,IPR_ICU_IRQ3=0x23,IPR_ICU_IRQ4=0x24,IPR_ICU_IRQ5=0x25,IPR_ICU_IRQ6=0x26,IPR_ICU_IRQ7=0x27,IPR_ICU_IRQ8=0x28,IPR_ICU_IRQ9=0x29,IPR_ICU_IRQ10=0x2A,IPR_ICU_IRQ11=0x2B,IPR_ICU_IRQ12=0x2C,IPR_ICU_IRQ13=0x2D,IPR_ICU_IRQ14=0x2E,IPR_ICU_IRQ15=0x2F,
IPR_USB_USBR0=0x3A,IPR_USB_USBR1=0x3B,
IPR_RTC_ALM=0x3C,
IPR_WDT_WOVI=0x40,
IPR_AD0_ADI0=0x44,
IPR_AD1_ADI1=0x45,
IPR_S12AD_ADI=0x48,
IPR_MTU0_TGIA0=0x51,IPR_MTU0_TGIB0=0x51,IPR_MTU0_TGIC0=0x51,IPR_MTU0_TGID0=0x51,IPR_MTU0_TCIV0=0x52,IPR_MTU0_TGIE0=0x52,IPR_MTU0_TGIF0=0x52,
IPR_MTU1_TGIA1=0x53,IPR_MTU1_TGIB1=0x53,IPR_MTU1_TCIV1=0x54,IPR_MTU1_TCIU1=0x54,
IPR_MTU2_TGIA2=0x55,IPR_MTU2_TGIB2=0x55,IPR_MTU2_TCIV2=0x56,IPR_MTU2_TCIU2=0x56,
IPR_MTU3_TGIA3=0x57,IPR_MTU3_TGIB3=0x57,IPR_MTU3_TGIC3=0x57,IPR_MTU3_TGID3=0x57,IPR_MTU3_TCIV3=0x58,
IPR_MTU4_TGIA4=0x59,IPR_MTU4_TGIB4=0x59,IPR_MTU4_TGIC4=0x59,IPR_MTU4_TGID4=0x59,IPR_MTU4_TCIV4=0x5A,
IPR_MTU5_TGIU5=0x5B,IPR_MTU5_TGIV5=0x5B,IPR_MTU5_TGIW5=0x5B,
IPR_MTU6_TGIA6=0x5C,IPR_MTU6_TGIB6=0x5C,IPR_MTU6_TGIC6=0x5C,IPR_MTU6_TGID6=0x5C,IPR_MTU6_TCIV6=0x5D,IPR_MTU6_TGIE6=0x5D,IPR_MTU6_TGIF6=0x5D,
IPR_MTU7_TGIA7=0x5E,IPR_MTU7_TGIB7=0x5E,IPR_MTU7_TCIV7=0x5F,IPR_MTU7_TCIU7=0x5F,
IPR_MTU8_TGIA8=0x60,IPR_MTU8_TGIB8=0x60,IPR_MTU8_TCIV8=0x61,IPR_MTU8_TCIU8=0x61,
IPR_MTU9_TGIA9=0x62,IPR_MTU9_TGIB9=0x62,IPR_MTU9_TGIC9=0x62,IPR_MTU9_TGID9=0x62,IPR_MTU9_TCIV9=0x63,
IPR_MTU10_TGIA10=0x64,IPR_MTU10_TGIB10=0x64,IPR_MTU10_TGIC10=0x64,IPR_MTU10_TGID10=0x64,IPR_MTU10_TCIV10=0x65,
IPR_MTU11_TGIU11=0x66,IPR_MTU11_TGIV11=0x66,IPR_MTU11_TGIW11=0x66,
IPR_POE_OEI1=0x67,IPR_POE_OEI2=0x67,IPR_POE_OEI3=0x67,IPR_POE_OEI4=0x67,
IPR_TMR0_CMIA0=0x68,IPR_TMR0_CMIB0=0x68,IPR_TMR0_OVI0=0x68,
IPR_TMR1_CMIA1=0x69,IPR_TMR1_CMIB1=0x69,IPR_TMR1_OVI1=0x69,
IPR_TMR2_CMIA2=0x6A,IPR_TMR2_CMIB2=0x6A,IPR_TMR2_OVI2=0x6A,
IPR_TMR3_CMIA3=0x6B,IPR_TMR3_CMIB3=0x6B,IPR_TMR3_OVI3=0x6B,
IPR_DMAC_DMAC0I=0x70,IPR_DMAC_DMAC1I=0x71,IPR_DMAC_DMAC2I=0x72,IPR_DMAC_DMAC3I=0x73,
IPR_EXDMAC_EXDMAC0I=0x74,IPR_EXDMAC_EXDMAC1I=0x75,
IPR_SCI0_ERI0=0x80,IPR_SCI0_RXI0=0x80,IPR_SCI0_TXI0=0x80,IPR_SCI0_TEI0=0x80,
IPR_SCI1_ERI1=0x81,IPR_SCI1_RXI1=0x81,IPR_SCI1_TXI1=0x81,IPR_SCI1_TEI1=0x81,
IPR_SCI2_ERI2=0x82,IPR_SCI2_RXI2=0x82,IPR_SCI2_TXI2=0x82,IPR_SCI2_TEI2=0x82,
IPR_SCI3_ERI3=0x83,IPR_SCI3_RXI3=0x83,IPR_SCI3_TXI3=0x83,IPR_SCI3_TEI3=0x83,
IPR_SCI5_ERI5=0x85,IPR_SCI5_RXI5=0x85,IPR_SCI5_TXI5=0x85,IPR_SCI5_TEI5=0x85,
IPR_SCI6_ERI6=0x86,IPR_SCI6_RXI6=0x86,IPR_SCI6_TXI6=0x86,IPR_SCI6_TEI6=0x86,
IPR_RIIC0_ICEEI0=0x88,IPR_RIIC0_ICRXI0=0x89,IPR_RIIC0_ICTXI0=0x8A,IPR_RIIC0_ICTEI0=0x8B,
IPR_RIIC1_ICEEI1=0x8C,IPR_RIIC1_ICRXI1=0x8D,IPR_RIIC1_ICTXI1=0x8E,IPR_RIIC1_ICTEI1=0x8F,
IPR_BSC_=0x00,
IPR_CMT0_=0x04,
IPR_CMT1_=0x05,
IPR_CMT2_=0x06,
IPR_CMT3_=0x07,
IPR_ETHER_=0x08,
IPR_RSPI0_=0x14,
IPR_RSPI1_=0x15,
IPR_CAN0_=0x18,
IPR_WDT_=0x40,
IPR_AD0_=0x44,
IPR_AD1_=0x45,
IPR_S12AD_=0x48,
IPR_MTU1_TGI=0x53,
IPR_MTU1_TCI=0x54,
IPR_MTU2_TGI=0x55,
IPR_MTU2_TCI=0x56,
IPR_MTU3_TGI=0x57,
IPR_MTU4_TGI=0x59,
IPR_MTU5_=0x5B,
IPR_MTU5_TGI=0x5B,
IPR_MTU7_TGI=0x5E,
IPR_MTU7_TCI=0x5F,
IPR_MTU8_TGI=0x60,
IPR_MTU8_TCI=0x61,
IPR_MTU9_TGI=0x62,
IPR_MTU10_TGI=0x64,
IPR_MTU11_=0x66,
IPR_MTU11_TGI=0x66,
IPR_POE_=0x67,
IPR_POE_OEI=0x67,
IPR_TMR0_=0x68,
IPR_TMR1_=0x69,
IPR_TMR2_=0x6A,
IPR_TMR3_=0x6B,
IPR_SCI0_=0x80,
IPR_SCI1_=0x81,
IPR_SCI2_=0x82,
IPR_SCI3_=0x83,
IPR_SCI5_=0x85,
IPR_SCI6_=0x86
};

#define	IEN_BSC_BUSERR		IEN0
#define	IEN_FCU_FIFERR		IEN5
#define	IEN_FCU_FRDYI		IEN7
#define	IEN_ICU_SWINT		IEN3
#define	IEN_CMT0_CMI0		IEN4
#define	IEN_CMT1_CMI1		IEN5
#define	IEN_CMT2_CMI2		IEN6
#define	IEN_CMT3_CMI3		IEN7
#define	IEN_ETHER_EINT		IEN0
#define	IEN_USB0_D0FIFO0	IEN4
#define	IEN_USB0_D1FIFO0	IEN5
#define	IEN_USB0_USBI0		IEN6
#define	IEN_USB1_D0FIFO1	IEN0
#define	IEN_USB1_D1FIFO1	IEN1
#define	IEN_USB1_USBI1		IEN2
#define	IEN_RSPI0_SPEI0		IEN4
#define	IEN_RSPI0_SPRI0		IEN5
#define	IEN_RSPI0_SPTI0		IEN6
#define	IEN_RSPI0_SPII0		IEN7
#define	IEN_RSPI1_SPEI1		IEN0
#define	IEN_RSPI1_SPRI1		IEN1
#define	IEN_RSPI1_SPTI1		IEN2
#define	IEN_RSPI1_SPII1		IEN3
#define	IEN_CAN0_ERS0		IEN0
#define	IEN_CAN0_RXF0		IEN1
#define	IEN_CAN0_TXF0		IEN2
#define	IEN_CAN0_RXM0		IEN3
#define	IEN_CAN0_TXM0		IEN4
#define	IEN_RTC_PRD			IEN6
#define	IEN_RTC_CUP			IEN7
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
#define	IEN_USB_USBR0		IEN2
#define	IEN_USB_USBR1		IEN3
#define	IEN_RTC_ALM			IEN4
#define	IEN_WDT_WOVI		IEN0
#define	IEN_AD0_ADI0		IEN2
#define	IEN_AD1_ADI1		IEN3
#define	IEN_S12AD_ADI		IEN6
#define	IEN_MTU0_TGIA0		IEN2
#define	IEN_MTU0_TGIB0		IEN3
#define	IEN_MTU0_TGIC0		IEN4
#define	IEN_MTU0_TGID0		IEN5
#define	IEN_MTU0_TCIV0		IEN6
#define	IEN_MTU0_TGIE0		IEN7
#define	IEN_MTU0_TGIF0		IEN0
#define	IEN_MTU1_TGIA1		IEN1
#define	IEN_MTU1_TGIB1		IEN2
#define	IEN_MTU1_TCIV1		IEN3
#define	IEN_MTU1_TCIU1		IEN4
#define	IEN_MTU2_TGIA2		IEN5
#define	IEN_MTU2_TGIB2		IEN6
#define	IEN_MTU2_TCIV2		IEN7
#define	IEN_MTU2_TCIU2		IEN0
#define	IEN_MTU3_TGIA3		IEN1
#define	IEN_MTU3_TGIB3		IEN2
#define	IEN_MTU3_TGIC3		IEN3
#define	IEN_MTU3_TGID3		IEN4
#define	IEN_MTU3_TCIV3		IEN5
#define	IEN_MTU4_TGIA4		IEN6
#define	IEN_MTU4_TGIB4		IEN7
#define	IEN_MTU4_TGIC4		IEN0
#define	IEN_MTU4_TGID4		IEN1
#define	IEN_MTU4_TCIV4		IEN2
#define	IEN_MTU5_TGIU5		IEN3
#define	IEN_MTU5_TGIV5		IEN4
#define	IEN_MTU5_TGIW5		IEN7
#define	IEN_MTU6_TGIA6		IEN6
#define	IEN_MTU6_TGIB6		IEN7
#define	IEN_MTU6_TGIC6		IEN0
#define	IEN_MTU6_TGID6		IEN1
#define	IEN_MTU6_TCIV6		IEN2
#define	IEN_MTU6_TGIE6		IEN3
#define	IEN_MTU6_TGIF6		IEN4
#define	IEN_MTU7_TGIA7		IEN5
#define	IEN_MTU7_TGIB7		IEN6
#define	IEN_MTU7_TCIV7		IEN7
#define	IEN_MTU7_TCIU7		IEN0
#define	IEN_MTU8_TGIA8		IEN1
#define	IEN_MTU8_TGIB8		IEN2
#define	IEN_MTU8_TCIV8		IEN3
#define	IEN_MTU8_TCIU8		IEN4
#define	IEN_MTU9_TGIA9		IEN5
#define	IEN_MTU9_TGIB9		IEN6
#define	IEN_MTU9_TGIC9		IEN7
#define	IEN_MTU9_TGID9		IEN0
#define	IEN_MTU9_TCIV9		IEN1
#define	IEN_MTU10_TGIA10	IEN2
#define	IEN_MTU10_TGIB10	IEN3
#define	IEN_MTU10_TGIC10	IEN4
#define	IEN_MTU10_TGID10	IEN5
#define	IEN_MTU10_TCIV10	IEN6
#define	IEN_MTU11_TGIU11	IEN7
#define	IEN_MTU11_TGIV11	IEN0
#define	IEN_MTU11_TGIW11	IEN1
#define	IEN_POE_OEI1		IEN2
#define	IEN_POE_OEI2		IEN3
#define	IEN_POE_OEI3		IEN4
#define	IEN_POE_OEI4		IEN5
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
#define	IEN_DMAC_DMAC0I		IEN6
#define	IEN_DMAC_DMAC1I		IEN7
#define	IEN_DMAC_DMAC2I		IEN0
#define	IEN_DMAC_DMAC3I		IEN1
#define	IEN_EXDMAC_EXDMAC0I	IEN2
#define	IEN_EXDMAC_EXDMAC1I	IEN3
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
#define	VECT_ICU_SWINT		27
#define	VECT_CMT0_CMI0		28
#define	VECT_CMT1_CMI1		29
#define	VECT_CMT2_CMI2		30
#define	VECT_CMT3_CMI3		31
#define	VECT_ETHER_EINT		32
#define	VECT_USB0_D0FIFO0	36
#define	VECT_USB0_D1FIFO0	37
#define	VECT_USB0_USBI0		38
#define	VECT_USB1_D0FIFO1	40
#define	VECT_USB1_D1FIFO1	41
#define	VECT_USB1_USBI1		42
#define	VECT_RSPI0_SPEI0	44
#define	VECT_RSPI0_SPRI0	45
#define	VECT_RSPI0_SPTI0	46
#define	VECT_RSPI0_SPII0	47
#define	VECT_RSPI1_SPEI1	48
#define	VECT_RSPI1_SPRI1	49
#define	VECT_RSPI1_SPTI1	50
#define	VECT_RSPI1_SPII1	51
#define	VECT_CAN0_ERS0		56
#define	VECT_CAN0_RXF0		57
#define	VECT_CAN0_TXF0		58
#define	VECT_CAN0_RXM0		59
#define	VECT_CAN0_TXM0		60
#define	VECT_RTC_PRD		62
#define	VECT_RTC_CUP		63
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
#define	VECT_USB_USBR0		90
#define	VECT_USB_USBR1		91
#define	VECT_RTC_ALM		92
#define	VECT_WDT_WOVI		96
#define	VECT_AD0_ADI0		98
#define	VECT_AD1_ADI1		99
#define	VECT_S12AD_ADI		102
#define	VECT_MTU0_TGIA0		114
#define	VECT_MTU0_TGIB0		115
#define	VECT_MTU0_TGIC0		116
#define	VECT_MTU0_TGID0		117
#define	VECT_MTU0_TCIV0		118
#define	VECT_MTU0_TGIE0		119
#define	VECT_MTU0_TGIF0		120
#define	VECT_MTU1_TGIA1		121
#define	VECT_MTU1_TGIB1		122
#define	VECT_MTU1_TCIV1		123
#define	VECT_MTU1_TCIU1		124
#define	VECT_MTU2_TGIA2		125
#define	VECT_MTU2_TGIB2		126
#define	VECT_MTU2_TCIV2		127
#define	VECT_MTU2_TCIU2		128
#define	VECT_MTU3_TGIA3		129
#define	VECT_MTU3_TGIB3		130
#define	VECT_MTU3_TGIC3		131
#define	VECT_MTU3_TGID3		132
#define	VECT_MTU3_TCIV3		133
#define	VECT_MTU4_TGIA4		134
#define	VECT_MTU4_TGIB4		135
#define	VECT_MTU4_TGIC4		136
#define	VECT_MTU4_TGID4		137
#define	VECT_MTU4_TCIV4		138
#define	VECT_MTU5_TGIU5		139
#define	VECT_MTU5_TGIV5		140
#define	VECT_MTU5_TGIW5		141
#define	VECT_MTU6_TGIA6		142
#define	VECT_MTU6_TGIB6		143
#define	VECT_MTU6_TGIC6		144
#define	VECT_MTU6_TGID6		145
#define	VECT_MTU6_TCIV6		146
#define	VECT_MTU6_TGIE6		147
#define	VECT_MTU6_TGIF6		148
#define	VECT_MTU7_TGIA7		149
#define	VECT_MTU7_TGIB7		150
#define	VECT_MTU7_TCIV7		151
#define	VECT_MTU7_TCIU7		152
#define	VECT_MTU8_TGIA8		153
#define	VECT_MTU8_TGIB8		154
#define	VECT_MTU8_TCIV8		155
#define	VECT_MTU8_TCIU8		156
#define	VECT_MTU9_TGIA9		157
#define	VECT_MTU9_TGIB9		158
#define	VECT_MTU9_TGIC9		159
#define	VECT_MTU9_TGID9		160
#define	VECT_MTU9_TCIV9		161
#define	VECT_MTU10_TGIA10	162
#define	VECT_MTU10_TGIB10	163
#define	VECT_MTU10_TGIC10	164
#define	VECT_MTU10_TGID10	165
#define	VECT_MTU10_TCIV10	166
#define	VECT_MTU11_TGIU11	167
#define	VECT_MTU11_TGIV11	168
#define	VECT_MTU11_TGIW11	169
#define	VECT_POE_OEI1		170
#define	VECT_POE_OEI2		171
#define	VECT_POE_OEI3		172
#define	VECT_POE_OEI4		173
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
#define	VECT_DMAC_DMAC0I	198
#define	VECT_DMAC_DMAC1I	199
#define	VECT_DMAC_DMAC2I	200
#define	VECT_DMAC_DMAC3I	201
#define	VECT_EXDMAC_EXDMAC0I	202
#define	VECT_EXDMAC_EXDMAC1I	203
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

#define	MSTP_EXDMAC	SYSTEM.MSTPCRA.BIT.MSTPA29
#define	MSTP_DMAC	SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_DMAC0	SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_DMAC1	SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_DMAC2	SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_DMAC3	SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_DTC	SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_AD0	SYSTEM.MSTPCRA.BIT.MSTPA23
#define	MSTP_AD1	SYSTEM.MSTPCRA.BIT.MSTPA22
#define	MSTP_DA		SYSTEM.MSTPCRA.BIT.MSTPA19
#define	MSTP_S12AD	SYSTEM.MSTPCRA.BIT.MSTPA17
#define	MSTP_CMT0	SYSTEM.MSTPCRA.BIT.MSTPA15
#define	MSTP_CMT1	SYSTEM.MSTPCRA.BIT.MSTPA15
#define	MSTP_CMT2	SYSTEM.MSTPCRA.BIT.MSTPA14
#define	MSTP_CMT3	SYSTEM.MSTPCRA.BIT.MSTPA14
#define	MSTP_PPG0	SYSTEM.MSTPCRA.BIT.MSTPA11
#define	MSTP_PPG1	SYSTEM.MSTPCRA.BIT.MSTPA10
#define	MSTP_MTUA	SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU0	SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU1	SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU2	SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU3	SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU4	SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU5	SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTUB	SYSTEM.MSTPCRA.BIT.MSTPA8
#define	MSTP_MTU6	SYSTEM.MSTPCRA.BIT.MSTPA8
#define	MSTP_MTU7	SYSTEM.MSTPCRA.BIT.MSTPA8
#define	MSTP_MTU8	SYSTEM.MSTPCRA.BIT.MSTPA8
#define	MSTP_MTU9	SYSTEM.MSTPCRA.BIT.MSTPA8
#define	MSTP_MTU10	SYSTEM.MSTPCRA.BIT.MSTPA8
#define	MSTP_MTU11	SYSTEM.MSTPCRA.BIT.MSTPA8
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
#define	MSTP_SCI5	SYSTEM.MSTPCRB.BIT.MSTPB26
#define	MSTP_SMCI5	SYSTEM.MSTPCRB.BIT.MSTPB26
#define	MSTP_SCI6	SYSTEM.MSTPCRB.BIT.MSTPB25
#define	MSTP_SMCI6	SYSTEM.MSTPCRB.BIT.MSTPB25
#define	MSTP_CRC	SYSTEM.MSTPCRB.BIT.MSTPB23
#define	MSTP_RIIC0	SYSTEM.MSTPCRB.BIT.MSTPB21
#define	MSTP_RIIC1	SYSTEM.MSTPCRB.BIT.MSTPB20
#define	MSTP_USB0	SYSTEM.MSTPCRB.BIT.MSTPB19
#define	MSTP_USB1	SYSTEM.MSTPCRB.BIT.MSTPB18
#define	MSTP_RSPI0	SYSTEM.MSTPCRB.BIT.MSTPB17
#define	MSTP_RSPI1	SYSTEM.MSTPCRB.BIT.MSTPB16
#define	MSTP_EDMAC	SYSTEM.MSTPCRB.BIT.MSTPB15
#define	MSTP_CAN0	SYSTEM.MSTPCRB.BIT.MSTPB0
#define	MSTP_RAM0	SYSTEM.MSTPCRC.BIT.MSTPC1
#define	MSTP_RAM1	SYSTEM.MSTPCRC.BIT.MSTPC0

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

#define	AD0		(*(volatile struct st_ad      __evenaccess *)0x88040)
#define	AD1		(*(volatile struct st_ad      __evenaccess *)0x88060)
#define	BSC		(*(volatile struct st_bsc     __evenaccess *)0x81300)
#define	CAN0	(*(volatile struct st_can     __evenaccess *)0x90200)
#define	CMT		(*(volatile struct st_cmt     __evenaccess *)0x88000)
#define	CMT0	(*(volatile struct st_cmt0    __evenaccess *)0x88002)
#define	CMT1	(*(volatile struct st_cmt0    __evenaccess *)0x88008)
#define	CMT2	(*(volatile struct st_cmt0    __evenaccess *)0x88012)
#define	CMT3	(*(volatile struct st_cmt0    __evenaccess *)0x88018)
#define	CRC		(*(volatile struct st_crc     __evenaccess *)0x88280)
#define	DA		(*(volatile struct st_da      __evenaccess *)0x880C0)
#define	DMAC	(*(volatile struct st_dmac    __evenaccess *)0x82200)
#define	DMAC0	(*(volatile struct st_dmac0   __evenaccess *)0x82000)
#define	DMAC1	(*(volatile struct st_dmac1   __evenaccess *)0x82040)
#define	DMAC2	(*(volatile struct st_dmac1   __evenaccess *)0x82080)
#define	DMAC3	(*(volatile struct st_dmac1   __evenaccess *)0x820C0)
#define	DTC		(*(volatile struct st_dtc     __evenaccess *)0x82400)
#define	EDMAC	(*(volatile struct st_edmac   __evenaccess *)0xC0000)
#define	ETHERC	(*(volatile struct st_etherc  __evenaccess *)0xC0100)
#define	EXDMAC	(*(volatile struct st_exdmac  __evenaccess *)0x82A00)
#define	EXDMAC0	(*(volatile struct st_exdmac0 __evenaccess *)0x82800)
#define	EXDMAC1	(*(volatile struct st_exdmac1 __evenaccess *)0x82840)
#define	FLASH	(*(volatile struct st_flash   __evenaccess *)0x8C288)
#define	ICU		(*(volatile struct st_icu     __evenaccess *)0x87000)
#define	IOPORT	(*(volatile struct st_ioport  __evenaccess *)0x8C100)
#define	IWDT	(*(volatile struct st_iwdt    __evenaccess *)0x88030)
#define	MTU0	(*(volatile struct st_mtu0    __evenaccess *)0x88700)
#define	MTU1	(*(volatile struct st_mtu1    __evenaccess *)0x88780)
#define	MTU2	(*(volatile struct st_mtu2    __evenaccess *)0x88800)
#define	MTU3	(*(volatile struct st_mtu3    __evenaccess *)0x88600)
#define	MTU4	(*(volatile struct st_mtu4    __evenaccess *)0x88600)
#define	MTU5	(*(volatile struct st_mtu5    __evenaccess *)0x88880)
#define	MTU6	(*(volatile struct st_mtu0    __evenaccess *)0x88B00)
#define	MTU7	(*(volatile struct st_mtu1    __evenaccess *)0x88B80)
#define	MTU8	(*(volatile struct st_mtu2    __evenaccess *)0x88C00)
#define	MTU9	(*(volatile struct st_mtu3    __evenaccess *)0x88A00)
#define	MTU10	(*(volatile struct st_mtu4    __evenaccess *)0x88A00)
#define	MTU11	(*(volatile struct st_mtu5    __evenaccess *)0x88C80)
#define	MTUA	(*(volatile struct st_mtua    __evenaccess *)0x8860A)
#define	MTUB	(*(volatile struct st_mtua    __evenaccess *)0x88A0A)
#define	POE		(*(volatile struct st_poe     __evenaccess *)0x88900)
#define	PORT0	(*(volatile struct st_port0   __evenaccess *)0x8C000)
#define	PORT1	(*(volatile struct st_port1   __evenaccess *)0x8C001)
#define	PORT2	(*(volatile struct st_port2   __evenaccess *)0x8C002)
#define	PORT3	(*(volatile struct st_port3   __evenaccess *)0x8C003)
#define	PORT4	(*(volatile struct st_port4   __evenaccess *)0x8C004)
#define	PORT5	(*(volatile struct st_port5   __evenaccess *)0x8C005)
#define	PORT6	(*(volatile struct st_port6   __evenaccess *)0x8C006)
#define	PORT7	(*(volatile struct st_port7   __evenaccess *)0x8C007)
#define	PORT8	(*(volatile struct st_port8   __evenaccess *)0x8C008)
#define	PORT9	(*(volatile struct st_port9   __evenaccess *)0x8C009)
#define	PORTA	(*(volatile struct st_porta   __evenaccess *)0x8C00A)
#define	PORTB	(*(volatile struct st_portb   __evenaccess *)0x8C00B)
#define	PORTC	(*(volatile struct st_portc   __evenaccess *)0x8C00C)
#define	PORTD	(*(volatile struct st_portd   __evenaccess *)0x8C00D)
#define	PORTE	(*(volatile struct st_porte   __evenaccess *)0x8C00E)
#define	PORTF	(*(volatile struct st_portf   __evenaccess *)0x8C00F)
#define	PORTG	(*(volatile struct st_portg   __evenaccess *)0x8C010)
#define	PPG0	(*(volatile struct st_ppg0    __evenaccess *)0x881E6)
#define	PPG1	(*(volatile struct st_ppg1    __evenaccess *)0x881F0)
#define	RIIC0	(*(volatile struct st_riic    __evenaccess *)0x88300)
#define	RIIC1	(*(volatile struct st_riic    __evenaccess *)0x88320)
#define	RSPI0	(*(volatile struct st_rspi    __evenaccess *)0x88380)
#define	RSPI1	(*(volatile struct st_rspi    __evenaccess *)0x883A0)
#define	RTC		(*(volatile struct st_rtc     __evenaccess *)0x8C400)
#define	S12AD	(*(volatile struct st_s12ad   __evenaccess *)0x89000)
#define	SCI0	(*(volatile struct st_sci     __evenaccess *)0x88240)
#define	SCI1	(*(volatile struct st_sci     __evenaccess *)0x88248)
#define	SCI2	(*(volatile struct st_sci     __evenaccess *)0x88250)
#define	SCI3	(*(volatile struct st_sci     __evenaccess *)0x88258)
#define	SCI5	(*(volatile struct st_sci     __evenaccess *)0x88268)
#define	SCI6	(*(volatile struct st_sci     __evenaccess *)0x88270)
#define	SMCI0	(*(volatile struct st_smci    __evenaccess *)0x88240)
#define	SMCI1	(*(volatile struct st_smci    __evenaccess *)0x88248)
#define	SMCI2	(*(volatile struct st_smci    __evenaccess *)0x88250)
#define	SMCI3	(*(volatile struct st_smci    __evenaccess *)0x88258)
#define	SMCI5	(*(volatile struct st_smci    __evenaccess *)0x88268)
#define	SMCI6	(*(volatile struct st_smci    __evenaccess *)0x88270)
#define	SYSTEM	(*(volatile struct st_system  __evenaccess *)0x80000)
#define	TMR0	(*(volatile struct st_tmr0    __evenaccess *)0x88200)
#define	TMR1	(*(volatile struct st_tmr1    __evenaccess *)0x88201)
#define	TMR2	(*(volatile struct st_tmr0    __evenaccess *)0x88210)
#define	TMR3	(*(volatile struct st_tmr1    __evenaccess *)0x88211)
#define	TMR01	(*(volatile struct st_tmr01   __evenaccess *)0x88204)
#define	TMR23	(*(volatile struct st_tmr01   __evenaccess *)0x88214)
#define	USB		(*(volatile struct st_usb     __evenaccess *)0xA0400)
#define	USB0	(*(volatile struct st_usb0    __evenaccess *)0xA0000)
#define	USB1	(*(volatile struct st_usb0    __evenaccess *)0xA0200)
#define	WDT		(*(volatile union un_wdt      __evenaccess *)0x88028)
#pragma bit_order
#pragma packoption
#endif
