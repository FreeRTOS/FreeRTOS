/********************************************************************************
*
* Device     : RX/RX700/RX71M
*
* File Name  : iodefine.h
*
* Abstract   : Definition of I/O Register
*
* History    : 0.10  (2014-03-22)  [Hardware Manual Revision : 0.10]
*            : 1.00  (2014-12-08)  [Hardware Manual Revision : 1.00]
*
* Note       : THIS IS A TYPICAL EXAMPLE.
*
* Copyright (C) 2014 Renesas Electronics Corporation.
*
*********************************************************************************/
/*                                                                              */
/*  DESCRIPTION : Definition of ICU Register                                    */
/*  CPU TYPE    : RX71M                                                         */
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
/*       MSTP(TPU4) = 0;    // TPU0,TPU1,TPU2,TPU3,TPU4,TPU5      expands to :  */
/*         SYSTEM.MSTPCRA.BIT.MSTPA13 = 0;                                      */
/*       MSTP(CMT3) = 0;    // CMT2,CMT3                          expands to :  */
/*         SYSTEM.MSTPCRA.BIT.MSTPA14 = 0;                                      */
/*                                                                              */
/*                                                                              */
/********************************************************************************/
#ifndef __RX71MIODEFINE_HEADER__
#define __RX71MIODEFINE_HEADER__
#pragma bit_order left
#pragma unpack
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
	char           wk3[4];
	union {
		unsigned short WORD;
		struct {
			unsigned short :2;
			unsigned short BPEB:2;
			unsigned short BPFB:2;
			unsigned short BPHB:2;
			unsigned short BPGB:2;
			unsigned short BPIB:2;
			unsigned short BPRO:2;
			unsigned short BPRA:2;
		} BIT;
	} BUSPRI;
	char           wk4[7408];
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
			unsigned long :2;
			unsigned long AWAIT:2;
			unsigned long :1;
			unsigned long WDOFF:3;
			unsigned long :1;
			unsigned long CSWOFF:3;
			unsigned long :1;
			unsigned long CSROFF:3;
		} BIT;
	} CS0WCR2;
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
			unsigned long :2;
			unsigned long AWAIT:2;
			unsigned long :1;
			unsigned long WDOFF:3;
			unsigned long :1;
			unsigned long CSWOFF:3;
			unsigned long :1;
			unsigned long CSROFF:3;
		} BIT;
	} CS1WCR2;
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
			unsigned long :2;
			unsigned long AWAIT:2;
			unsigned long :1;
			unsigned long WDOFF:3;
			unsigned long :1;
			unsigned long CSWOFF:3;
			unsigned long :1;
			unsigned long CSROFF:3;
		} BIT;
	} CS2WCR2;
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
			unsigned long :2;
			unsigned long AWAIT:2;
			unsigned long :1;
			unsigned long WDOFF:3;
			unsigned long :1;
			unsigned long CSWOFF:3;
			unsigned long :1;
			unsigned long CSROFF:3;
		} BIT;
	} CS3WCR2;
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
			unsigned long :2;
			unsigned long AWAIT:2;
			unsigned long :1;
			unsigned long WDOFF:3;
			unsigned long :1;
			unsigned long CSWOFF:3;
			unsigned long :1;
			unsigned long CSROFF:3;
		} BIT;
	} CS4WCR2;
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
			unsigned long :2;
			unsigned long AWAIT:2;
			unsigned long :1;
			unsigned long WDOFF:3;
			unsigned long :1;
			unsigned long CSWOFF:3;
			unsigned long :1;
			unsigned long CSROFF:3;
		} BIT;
	} CS5WCR2;
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
			unsigned long :2;
			unsigned long AWAIT:2;
			unsigned long :1;
			unsigned long WDOFF:3;
			unsigned long :1;
			unsigned long CSWOFF:3;
			unsigned long :1;
			unsigned long CSROFF:3;
		} BIT;
	} CS6WCR2;
	char           wk11[6];
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
			unsigned long :2;
			unsigned long AWAIT:2;
			unsigned long :1;
			unsigned long WDOFF:3;
			unsigned long :1;
			unsigned long CSWOFF:3;
			unsigned long :1;
			unsigned long CSROFF:3;
		} BIT;
	} CS7WCR2;
	char           wk12[1926];
	union {
		unsigned short WORD;
		struct {
			unsigned short :3;
			unsigned short MPXEN:1;
			unsigned short :3;
			unsigned short EMODE:1;
			unsigned short :2;
			unsigned short BSIZE:2;
			unsigned short :3;
			unsigned short EXENB:1;
		} BIT;
	} CS0CR;
	char           wk13[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS0REC;
	char           wk14[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :3;
			unsigned short MPXEN:1;
			unsigned short :3;
			unsigned short EMODE:1;
			unsigned short :2;
			unsigned short BSIZE:2;
			unsigned short :3;
			unsigned short EXENB:1;
		} BIT;
	} CS1CR;
	char           wk15[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS1REC;
	char           wk16[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :3;
			unsigned short MPXEN:1;
			unsigned short :3;
			unsigned short EMODE:1;
			unsigned short :2;
			unsigned short BSIZE:2;
			unsigned short :3;
			unsigned short EXENB:1;
		} BIT;
	} CS2CR;
	char           wk17[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS2REC;
	char           wk18[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :3;
			unsigned short MPXEN:1;
			unsigned short :3;
			unsigned short EMODE:1;
			unsigned short :2;
			unsigned short BSIZE:2;
			unsigned short :3;
			unsigned short EXENB:1;
		} BIT;
	} CS3CR;
	char           wk19[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS3REC;
	char           wk20[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :3;
			unsigned short MPXEN:1;
			unsigned short :3;
			unsigned short EMODE:1;
			unsigned short :2;
			unsigned short BSIZE:2;
			unsigned short :3;
			unsigned short EXENB:1;
		} BIT;
	} CS4CR;
	char           wk21[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS4REC;
	char           wk22[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :3;
			unsigned short MPXEN:1;
			unsigned short :3;
			unsigned short EMODE:1;
			unsigned short :2;
			unsigned short BSIZE:2;
			unsigned short :3;
			unsigned short EXENB:1;
		} BIT;
	} CS5CR;
	char           wk23[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS5REC;
	char           wk24[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :3;
			unsigned short MPXEN:1;
			unsigned short :3;
			unsigned short EMODE:1;
			unsigned short :2;
			unsigned short BSIZE:2;
			unsigned short :3;
			unsigned short EXENB:1;
		} BIT;
	} CS6CR;
	char           wk25[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS6REC;
	char           wk26[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :3;
			unsigned short MPXEN:1;
			unsigned short :3;
			unsigned short EMODE:1;
			unsigned short :2;
			unsigned short BSIZE:2;
			unsigned short :3;
			unsigned short EXENB:1;
		} BIT;
	} CS7CR;
	char           wk27[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short WRCV:4;
			unsigned short :4;
			unsigned short RRCV:4;
		} BIT;
	} CS7REC;
	char           wk28[4];
	union {
		unsigned short WORD;
		struct {
			unsigned short RCVENM7:1;
			unsigned short RCVENM6:1;
			unsigned short RCVENM5:1;
			unsigned short RCVENM4:1;
			unsigned short RCVENM3:1;
			unsigned short RCVENM2:1;
			unsigned short RCVENM1:1;
			unsigned short RCVENM0:1;
			unsigned short RCVEN7:1;
			unsigned short RCVEN6:1;
			unsigned short RCVEN5:1;
			unsigned short RCVEN4:1;
			unsigned short RCVEN3:1;
			unsigned short RCVEN2:1;
			unsigned short RCVEN1:1;
			unsigned short RCVEN0:1;
		} BIT;
	} CSRECEN;
	char           wk29[894];
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
	char           wk30[13];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char SFEN:1;
		} BIT;
	} SDSELF;
	char           wk31[3];
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
	char           wk32[9];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char INIRQ:1;
		} BIT;
	} SDICR;
	char           wk33[3];
	union {
		unsigned short WORD;
		struct {
			unsigned short :5;
			unsigned short PRC:3;
			unsigned short ARFC:4;
			unsigned short ARFI:4;
		} BIT;
	} SDIR;
	char           wk34[26];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char MXC:2;
		} BIT;
	} SDADR;
	char           wk35[3];
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
	char           wk36[6];
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

struct st_cac {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char CFME:1;
		} BIT;
	} CACR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char EDGES:2;
			unsigned char TCSS:2;
			unsigned char FMCS:3;
			unsigned char CACREFE:1;
		} BIT;
	} CACR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char DFS:2;
			unsigned char RCDS:2;
			unsigned char RSCS:3;
			unsigned char RPS:1;
		} BIT;
	} CACR2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char OVFFCL:1;
			unsigned char MENDFCL:1;
			unsigned char FERRFCL:1;
			unsigned char :1;
			unsigned char OVFIE:1;
			unsigned char MENDIE:1;
			unsigned char FERRIE:1;
		} BIT;
	} CAICR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char OVFF:1;
			unsigned char MENDF:1;
			unsigned char FERRF:1;
		} BIT;
	} CASTR;
	char           wk0[1];
	unsigned short CAULVR;
	unsigned short CALLVR;
	unsigned short CACNTBR;
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
			unsigned char MB31:1;
			unsigned char MB30:1;
			unsigned char MB29:1;
			unsigned char MB28:1;
			unsigned char MB27:1;
			unsigned char MB26:1;
			unsigned char MB25:1;
			unsigned char MB24:1;
			unsigned char MB23:1;
			unsigned char MB22:1;
			unsigned char MB21:1;
			unsigned char MB20:1;
			unsigned char MB19:1;
			unsigned char MB18:1;
			unsigned char MB17:1;
			unsigned char MB16:1;
			unsigned char MB15:1;
			unsigned char MB14:1;
			unsigned char MB13:1;
			unsigned char MB12:1;
			unsigned char MB11:1;
			unsigned char MB10:1;
			unsigned char MB9:1;
			unsigned char MB8:1;
			unsigned char MB7:1;
			unsigned char MB6:1;
			unsigned char MB5:1;
			unsigned char MB4:1;
			unsigned char MB3:1;
			unsigned char MB2:1;
			unsigned char MB1:1;
			unsigned char MB0:1;
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
			unsigned char MB31:1;
			unsigned char MB30:1;
			unsigned char MB29:1;
			unsigned char MB28:1;
			unsigned char MB27:1;
			unsigned char MB26:1;
			unsigned char MB25:1;
			unsigned char MB24:1;
			unsigned char MB23:1;
			unsigned char MB22:1;
			unsigned char MB21:1;
			unsigned char MB20:1;
			unsigned char MB19:1;
			unsigned char MB18:1;
			unsigned char MB17:1;
			unsigned char MB16:1;
			unsigned char MB15:1;
			unsigned char MB14:1;
			unsigned char MB13:1;
			unsigned char MB12:1;
			unsigned char MB11:1;
			unsigned char MB10:1;
			unsigned char MB9:1;
			unsigned char MB8:1;
			unsigned char MB7:1;
			unsigned char MB6:1;
			unsigned char MB5:1;
			unsigned char MB4:1;
			unsigned char MB3:1;
			unsigned char MB2:1;
			unsigned char MB1:1;
			unsigned char MB0:1;
		} BIT;
	} MIER;
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
				unsigned char TRMREQ:1;
				unsigned char RECREQ:1;
				unsigned char :1;
				unsigned char ONESHOT:1;
				unsigned char :1;
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
			unsigned long :7;
			unsigned long CCLKS:1;
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

struct st_cmtw {
	union {
		unsigned short WORD;
		struct {
			unsigned short :15;
			unsigned short STR:1;
		} BIT;
	} CMWSTR;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short CCLR:3;
			unsigned short :3;
			unsigned short CMS:1;
			unsigned short :1;
			unsigned short OC1IE:1;
			unsigned short OC0IE:1;
			unsigned short IC1IE:1;
			unsigned short IC0IE:1;
			unsigned short CMWIE:1;
			unsigned short :1;
			unsigned short CKS:2;
		} BIT;
	} CMWCR;
	char           wk1[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short CMWE:1;
			unsigned short :1;
			unsigned short OC1E:1;
			unsigned short OC0E:1;
			unsigned short OC1:2;
			unsigned short OC0:2;
			unsigned short :2;
			unsigned short IC1E:1;
			unsigned short IC0E:1;
			unsigned short IC1:2;
			unsigned short IC0:2;
		} BIT;
	} CMWIOR;
	char           wk2[6];
	unsigned long  CMWCNT;
	unsigned long  CMWCOR;
	unsigned long  CMWICR0;
	unsigned long  CMWICR1;
	unsigned long  CMWOCR0;
	unsigned long  CMWOCR1;
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
	union {
		unsigned char BYTE;
		struct {
			unsigned char DAADST:1;
		} BIT;
	} DAADSCR;
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char DAAMP1:1;
			unsigned char DAAMP0:1;
		} BIT;
	} DAAMPCR;
	char           wk1[17783];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char AMADSEL1:1;
		} BIT;
	} DAADUSR;
};

struct st_dmac {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DMST:1;
		} BIT;
	} DMAST;
	char           wk0[3];
	union {
		unsigned char BYTE;
		struct {
			unsigned char DMIS7:1;
			unsigned char DMIS6:1;
			unsigned char DMIS5:1;
			unsigned char DMIS4:1;
		} BIT;
	} DMIST;
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

struct st_doc {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char DOPCFCL:1;
			unsigned char DOPCF:1;
			unsigned char DOPCIE:1;
			unsigned char :1;
			unsigned char DCSEL:1;
			unsigned char OMS:2;
		} BIT;
	} DOCR;
	char           wk0[1];
	unsigned short DODIR;
	unsigned short DODSR;
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

struct st_eccram {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char RAMMOD:2;
		} BIT;
	} ECCRAMMODE;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char ECC2ERR:1;
		} BIT;
	} ECCRAM2STS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char ECC1STSEN:1;
		} BIT;
	} ECCRAM1STSEN;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char ECC1ERR:1;
		} BIT;
	} ECCRAM1STS;
//	union {
//		unsigned char BYTE;
//		struct {
//			unsigned char KW:7;
//			unsigned char PRCR:1;
//		} BIT;
//	} ECCRAMPRCR;
	unsigned char ECCRAMPRCR;
	char           wk0[3];
	union {
		unsigned long LONG;
		struct {
			unsigned long :17;
			unsigned long ECC2EAD:12;
		} BIT;
	} ECCRAM2ECAD;
	union {
		unsigned long LONG;
		struct {
			unsigned long :17;
			unsigned long ECC1EAD:12;
		} BIT;
	} ECCRAM1ECAD;
//	union {
//		unsigned char BYTE;
//		struct {
//			unsigned char KW2:7;
//			unsigned char PRCR2:1;
//		} BIT;
//	} ECCRAMPRCR2;
	unsigned char ECCRAMPRCR2;
	char           wk1[3];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char TSTBYP:1;
		} BIT;
	} ECCRAMETST;
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
			unsigned long :24;
			unsigned long RMAFCE:1;
			unsigned long :2;
			unsigned long RRFCE:1;
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
			unsigned long :31;
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
			unsigned long ELB:1;
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

struct st_elc {
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELCON:1;
		} BIT;
	} ELCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR0;
	char           wk0[2];
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR3;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR4;
	char           wk1[2];
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR7;
	char           wk2[2];
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR10;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR11;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR12;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR13;
	char           wk3[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR15;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR16;
	char           wk4[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR18;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR19;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR20;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR21;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR22;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR23;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR24;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR25;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR26;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR27;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR28;
	char           wk5[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char MTU3MD:2;
			unsigned char :4;
			unsigned char MTU0MD:2;
		} BIT;
	} ELOPA;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char MTU4MD:2;
		} BIT;
	} ELOPB;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char CMT1MD:2;
		} BIT;
	} ELOPC;
	union {
		unsigned char BYTE;
		struct {
			unsigned char TMR3MD:2;
			unsigned char TMR2MD:2;
			unsigned char TMR1MD:2;
			unsigned char TMR0MD:2;
		} BIT;
	} ELOPD;
	union {
		unsigned char BYTE;
		struct {
			unsigned char PGR7:1;
			unsigned char PGR6:1;
			unsigned char PGR5:1;
			unsigned char PGR4:1;
			unsigned char PGR3:1;
			unsigned char PGR2:1;
			unsigned char PGR1:1;
			unsigned char PGR0:1;
		} BIT;
	} PGR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char PGR7:1;
			unsigned char PGR6:1;
			unsigned char PGR5:1;
			unsigned char PGR4:1;
			unsigned char PGR3:1;
			unsigned char PGR2:1;
			unsigned char PGR1:1;
			unsigned char PGR0:1;
		} BIT;
	} PGR2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char PGCO:3;
			unsigned char :1;
			unsigned char PGCOVE:1;
			unsigned char PGCI:2;
		} BIT;
	} PGC1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char PGCO:3;
			unsigned char :1;
			unsigned char PGCOVE:1;
			unsigned char PGCI:2;
		} BIT;
	} PGC2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char PDBF7:1;
			unsigned char PDBF6:1;
			unsigned char PDBF5:1;
			unsigned char PDBF4:1;
			unsigned char PDBF3:1;
			unsigned char PDBF2:1;
			unsigned char PDBF1:1;
			unsigned char PDBF0:1;
		} BIT;
	} PDBF1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char PDBF7:1;
			unsigned char PDBF6:1;
			unsigned char PDBF5:1;
			unsigned char PDBF4:1;
			unsigned char PDBF3:1;
			unsigned char PDBF2:1;
			unsigned char PDBF1:1;
			unsigned char PDBF0:1;
		} BIT;
	} PDBF2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char PSM:2;
			unsigned char PSP:2;
			unsigned char PSB:3;
		} BIT;
	} PEL0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char PSM:2;
			unsigned char PSP:2;
			unsigned char PSB:3;
		} BIT;
	} PEL1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char PSM:2;
			unsigned char PSP:2;
			unsigned char PSB:3;
		} BIT;
	} PEL2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char PSM:2;
			unsigned char PSP:2;
			unsigned char PSB:3;
		} BIT;
	} PEL3;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char WI:1;
//			unsigned char WE:1;
//			unsigned char :5;
//			unsigned char SEG:1;
//		} BIT;
	} ELSEGR;
	char           wk6[3];
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR33;
	char           wk7[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR35;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR36;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR37;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR38;
	char           wk8[2];
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR41;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR42;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR43;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR44;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ELS:8;
		} BIT;
	} ELSR45;
	char           wk9[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char TPU3MD:2;
			unsigned char TPU2MD:2;
			unsigned char TPU1MD:2;
			unsigned char TPU0MD:2;
		} BIT;
	} ELOPF;
	char           wk10[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char CMTW0MD:2;
		} BIT;
	} ELOPH;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char GPT1MD:3;
			unsigned char :1;
			unsigned char GPT0MD:3;
		} BIT;
	} ELOPI;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char GPT3MD:3;
			unsigned char :1;
			unsigned char GPT2MD:3;
		} BIT;
	} ELOPJ;
};

struct st_eptpc {
	union {
		unsigned long LONG;
		struct {
			unsigned long :31;
			unsigned long RESET:1;
		} BIT;
	} PTRSTR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :21;
			unsigned long SCLKSEL:3;
			unsigned long :5;
			unsigned long SCLKDIV:3;
		} BIT;
	} STCSELR;
	char           wk0[15096];
//	union {
//	unsigned long LONG;
//		struct {
//			unsigned long :10;
//			unsigned long CYC5:1;
//			unsigned long CYC4:1;
//			unsigned long CYC3:1;
//			unsigned long CYC2:1;
//			unsigned long CYC1:1;
//			unsigned long CYC0:1;
//			unsigned long :12;
//			unsigned long PRC:1;
//			unsigned long SY1:1;
//			unsigned long SY0:1;
//			unsigned long ST:1;
//		} BIT;
//	} MIESR;
	unsigned long MIESR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :10;
			unsigned long CYC5:1;
			unsigned long CYC4:1;
			unsigned long CYC3:1;
			unsigned long CYC2:1;
			unsigned long CYC1:1;
			unsigned long CYC0:1;
			unsigned long :12;
			unsigned long PR:1;
			unsigned long SY1:1;
			unsigned long SY0:1;
			unsigned long ST:1;
		} BIT;
	} MIEIPR;
	char           wk1[8];
	union {
		unsigned long LONG;
		struct {
			unsigned long :7;
			unsigned long PLSN:1;
			unsigned long :7;
			unsigned long PLSP:1;
			unsigned long :2;
			unsigned long CYCN5:1;
			unsigned long CYCN4:1;
			unsigned long CYCN3:1;
			unsigned long CYCN2:1;
			unsigned long CYCN1:1;
			unsigned long CYCN0:1;
			unsigned long :2;
			unsigned long CYCP5:1;
			unsigned long CYCP4:1;
			unsigned long CYCP3:1;
			unsigned long CYCP2:1;
			unsigned long CYCP1:1;
			unsigned long CYCP0:1;
		} BIT;
	} ELIPPR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :7;
			unsigned long PLSN:1;
			unsigned long :7;
			unsigned long PLSP:1;
			unsigned long :2;
			unsigned long CYCN5:1;
			unsigned long CYCN4:1;
			unsigned long CYCN3:1;
			unsigned long CYCN2:1;
			unsigned long CYCN1:1;
			unsigned long CYCN0:1;
			unsigned long :2;
			unsigned long CYCP5:1;
			unsigned long CYCP4:1;
			unsigned long CYCP3:1;
			unsigned long CYCP2:1;
			unsigned long CYCP1:1;
			unsigned long CYCP0:1;
		} BIT;
	} ELIPACR;
	char           wk2[40];
//	union {
//		unsigned long LONG;
//		struct {
//			unsigned long :27;
//			unsigned long W10D:1;
//			unsigned long SYNTOUT:1;
//			unsigned long :1;
//			unsigned long SYNCOUT:1;
//			unsigned long SYNC:1;
//		} BIT;
//	} STSR;
	unsigned long STSR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :27;
			unsigned long W10D:1;
			unsigned long SYNTOUT:1;
			unsigned long :1;
			unsigned long SYNCOUT:1;
			unsigned long SYNC:1;
		} BIT;
	} STIPR;
	char           wk3[8];
	union {
		unsigned long LONG;
		struct {
			unsigned long :30;
			unsigned long STCF:2;
		} BIT;
	} STCFR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :2;
			unsigned long ALEN1:1;
			unsigned long ALEN0:1;
			unsigned long :4;
			unsigned long DVTH:4;
			unsigned long SYTH:4;
			unsigned long W10S:1;
			unsigned long :1;
			unsigned long CMOD:1;
			unsigned long :5;
			unsigned long WINT:8;
		} BIT;
	} STMR;
	unsigned long  SYNTOR;
	char           wk4[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :26;
			unsigned long IPTSEL5:1;
			unsigned long IPTSEL4:1;
			unsigned long IPTSEL3:1;
			unsigned long IPTSEL2:1;
			unsigned long IPTSEL1:1;
			unsigned long IPTSEL0:1;
		} BIT;
	} IPTSELR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :26;
			unsigned long MINTEN5:1;
			unsigned long MINTEN4:1;
			unsigned long MINTEN3:1;
			unsigned long MINTEN2:1;
			unsigned long MINTEN1:1;
			unsigned long MINTEN0:1;
		} BIT;
	} MITSELR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :26;
			unsigned long ELTDIS5:1;
			unsigned long ELTDIS4:1;
			unsigned long ELTDIS3:1;
			unsigned long ELTDIS2:1;
			unsigned long ELTDIS1:1;
			unsigned long ELTDIS0:1;
		} BIT;
	} ELTSELR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :31;
			unsigned long SYSEL:1;
		} BIT;
	} STCHSELR;
	char           wk5[16];
	union {
		unsigned long LONG;
		struct {
			unsigned long :31;
			unsigned long STR:1;
		} BIT;
	} SYNSTARTR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :31;
			unsigned long LOAD:1;
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
			unsigned long :16;
			unsigned long VALU:16;
		} BIT;
	} LCIVRU;
	unsigned long  LCIVRM;
	unsigned long  LCIVRL;
	char           wk8[104];
	union {
		unsigned long LONG;
		struct {
			unsigned long :31;
			unsigned long GW10:1;
		} BIT;
	} GETW10R;
	union {
		unsigned long LONG;
		struct {
			unsigned long :1;
			unsigned long LMTU:31;
		} BIT;
	} PLIMITRU;
	unsigned long  PLIMITRM;
	unsigned long  PLIMITRL;
	union {
		unsigned long LONG;
		struct {
			unsigned long :1;
			unsigned long LMTU:31;
		} BIT;
	} MLIMITRU;
	unsigned long  MLIMITRM;
	unsigned long  MLIMITRL;
	union {
		unsigned long LONG;
		struct {
			unsigned long :31;
			unsigned long INFO:1;
		} BIT;
	} GETINFOR;
	char           wk9[44];
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long CNTU:16;
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
			unsigned long :2;
			unsigned long CYC:30;
		} BIT;
	} TMCYCR0;
	union {
		unsigned long LONG;
		struct {
			unsigned long :3;
			unsigned long WTH:29;
		} BIT;
	} TMPLSR0;
	unsigned long  TMSTTRU1;
	unsigned long  TMSTTRL1;
	union {
		unsigned long LONG;
		struct {
			unsigned long :2;
			unsigned long CYC:30;
		} BIT;
	} TMCYCR1;
	union {
		unsigned long LONG;
		struct {
			unsigned long :3;
			unsigned long WTH:29;
		} BIT;
	} TMPLSR1;
	unsigned long  TMSTTRU2;
	unsigned long  TMSTTRL2;
	union {
		unsigned long LONG;
		struct {
			unsigned long :2;
			unsigned long CYC:30;
		} BIT;
	} TMCYCR2;
	union {
		unsigned long LONG;
		struct {
			unsigned long :3;
			unsigned long WTH:29;
		} BIT;
	} TMPLSR2;
	unsigned long  TMSTTRU3;
	unsigned long  TMSTTRL3;
	union {
		unsigned long LONG;
		struct {
			unsigned long :2;
			unsigned long CYC:30;
		} BIT;
	} TMCYCR3;
	union {
		unsigned long LONG;
		struct {
			unsigned long :3;
			unsigned long WTH:29;
		} BIT;
	} TMPLSR3;
	unsigned long  TMSTTRU4;
	unsigned long  TMSTTRL4;
	union {
		unsigned long LONG;
		struct {
			unsigned long :2;
			unsigned long CYC:30;
		} BIT;
	} TMCYCR4;
	union {
		unsigned long LONG;
		struct {
			unsigned long :3;
			unsigned long WTH:29;
		} BIT;
	} TMPLSR4;
	unsigned long  TMSTTRU5;
	unsigned long  TMSTTRL5;
	union {
		unsigned long LONG;
		struct {
			unsigned long :2;
			unsigned long CYC:30;
		} BIT;
	} TMCYCR5;
	union {
		unsigned long LONG;
		struct {
			unsigned long :3;
			unsigned long WTH:29;
		} BIT;
	} TMPLSR5;
	char           wk13[28];
	union {
		unsigned long LONG;
		struct {
			unsigned long :26;
			unsigned long EN5:1;
			unsigned long EN4:1;
			unsigned long EN3:1;
			unsigned long EN2:1;
			unsigned long EN1:1;
			unsigned long EN0:1;
		} BIT;
	} TMSTARTR;
	char           wk14[128];
//	union {
//		unsigned long LONG;
//		struct {
//			unsigned long :2;
//			unsigned long URE1:1;
//			unsigned long URE0:1;
//			unsigned long :19;
//			unsigned long MACE:1;
//			unsigned long :4;
//			unsigned long OVRE3:1;
//			unsigned long OVRE2:1;
//			unsigned long OVRE1:1;
//			unsigned long OVRE0:1;
//		} BIT;
//	} PRSR;
	unsigned long PRSR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :2;
			unsigned long URE1:1;
			unsigned long URE0:1;
			unsigned long :19;
			unsigned long MACE:1;
			unsigned long :4;
			unsigned long OVRE3:1;
			unsigned long OVRE2:1;
			unsigned long OVRE1:1;
			unsigned long OVRE0:1;
		} BIT;
	} PRIPR;
	char           wk15[8];
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long MACU:24;
		} BIT;
	} PRMACRU0;
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long MACL:24;
		} BIT;
	} PRMACRL0;
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long MACU:24;
		} BIT;
	} PRMACRU1;
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long MACL:24;
		} BIT;
	} PRMACRL1;
	union {
		unsigned long LONG;
		struct {
			unsigned long :30;
			unsigned long TDIS:2;
		} BIT;
	} TRNDISR;
	char           wk16[12];
	union {
		unsigned long LONG;
		struct {
			unsigned long :22;
			unsigned long FWD1:1;
			unsigned long FWD0:1;
			unsigned long :7;
			unsigned long MOD:1;
		} BIT;
	} TRNMR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :21;
			unsigned long THVAL:11;
		} BIT;
	} TRNCTTDR;
};

struct st_eptpc0 {
//	union {
//		unsigned long LONG;
//		struct {
//			unsigned long :14;
//			unsigned long GENDN:1;
//			unsigned long RESDN:1;
//			unsigned long :1;
//			unsigned long INFABT:1;
//			unsigned long :1;
//			unsigned long RECLP:1;
//			unsigned long :5;
//			unsigned long DRQOVR:1;
//			unsigned long INTDEV:1;
//			unsigned long DRPTO:1;
//			unsigned long :1;
//			unsigned long MPDUD:1;
//			unsigned long INTCHG:1;
//			unsigned long OFMUD:1;
//		} BIT;
//	} SYSR;
	unsigned long SYSR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :14;
			unsigned long GENDN:1;
			unsigned long RESDN:1;
			unsigned long :1;
			unsigned long INFABT:1;
			unsigned long :1;
			unsigned long RECLP:1;
			unsigned long :5;
			unsigned long DRQOVR:1;
			unsigned long INTDEV:1;
			unsigned long DRPTO:1;
			unsigned long :1;
			unsigned long MPDUD:1;
			unsigned long INTCHG:1;
			unsigned long OFMUD:1;
		} BIT;
	} SYIPR;
	char           wk0[8];
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long MACU:24;
		} BIT;
	} SYMACRU;
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long MACL:24;
		} BIT;
	} SYMACRL;
	unsigned long  SYLLCCTLR;
	unsigned long  SYIPADDRR;
	char           wk1[32];
	union {
		unsigned long LONG;
		struct {
			unsigned long :24;
			unsigned long TRSP:4;
			unsigned long VER:4;
		} BIT;
	} SYSPVRR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :24;
			unsigned long DNUM:8;
		} BIT;
	} SYDOMR;
	char           wk2[8];
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long FLAG15:1;
			unsigned long FLAG14:1;
			unsigned long FLAG13:1;
			unsigned long FLAG12:1;
			unsigned long FLAG11:1;
			unsigned long FLAG10:1;
			unsigned long FLAG9:1;
			unsigned long FLAG8:1;
			unsigned long FLAG7:1;
			unsigned long FLAG6:1;
			unsigned long FLAG5:1;
			unsigned long FLAG4:1;
			unsigned long FLAG3:1;
			unsigned long FLAG2:1;
			unsigned long FLAG1:1;
			unsigned long FLAG0:1;
		} BIT;
	} ANFR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long FLAG15:1;
			unsigned long FLAG14:1;
			unsigned long FLAG13:1;
			unsigned long FLAG12:1;
			unsigned long FLAG11:1;
			unsigned long FLAG10:1;
			unsigned long FLAG9:1;
			unsigned long FLAG8:1;
			unsigned long FLAG7:1;
			unsigned long FLAG6:1;
			unsigned long FLAG5:1;
			unsigned long FLAG4:1;
			unsigned long FLAG3:1;
			unsigned long FLAG2:1;
			unsigned long FLAG1:1;
			unsigned long FLAG0:1;
		} BIT;
	} SYNFR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long FLAG15:1;
			unsigned long FLAG14:1;
			unsigned long FLAG13:1;
			unsigned long FLAG12:1;
			unsigned long FLAG11:1;
			unsigned long FLAG10:1;
			unsigned long FLAG9:1;
			unsigned long FLAG8:1;
			unsigned long FLAG7:1;
			unsigned long FLAG6:1;
			unsigned long FLAG5:1;
			unsigned long FLAG4:1;
			unsigned long FLAG3:1;
			unsigned long FLAG2:1;
			unsigned long FLAG1:1;
			unsigned long FLAG0:1;
		} BIT;
	} DYRQFR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long FLAG15:1;
			unsigned long FLAG14:1;
			unsigned long FLAG13:1;
			unsigned long FLAG12:1;
			unsigned long FLAG11:1;
			unsigned long FLAG10:1;
			unsigned long FLAG9:1;
			unsigned long FLAG8:1;
			unsigned long FLAG7:1;
			unsigned long FLAG6:1;
			unsigned long FLAG5:1;
			unsigned long FLAG4:1;
			unsigned long FLAG3:1;
			unsigned long FLAG2:1;
			unsigned long FLAG1:1;
			unsigned long FLAG0:1;
		} BIT;
	} DYRPFR;
	unsigned long  SYCIDRU;
	unsigned long  SYCIDRL;
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long PNUM:16;
		} BIT;
	} SYPNUMR;
	char           wk3[20];
	union {
		unsigned long LONG;
		struct {
			unsigned long :29;
			unsigned long ANUP:1;
			unsigned long STUP:1;
			unsigned long BMUP:1;
		} BIT;
	} SYRVLDR;
	char           wk4[12];
	union {
		unsigned long LONG;
		struct {
			unsigned long :1;
			unsigned long PDFUP:3;
			unsigned long :1;
			unsigned long PDRP:3;
			unsigned long :1;
			unsigned long PDRQ:3;
			unsigned long :1;
			unsigned long DRP:3;
			unsigned long :1;
			unsigned long DRQ:3;
			unsigned long :1;
			unsigned long FUP:3;
			unsigned long :1;
			unsigned long SYNC:3;
			unsigned long :2;
			unsigned long ANCE:2;
		} BIT;
	} SYRFL1R;
	union {
		unsigned long LONG;
		struct {
			unsigned long :2;
			unsigned long ILL:2;
			unsigned long :22;
			unsigned long SIG:2;
			unsigned long :2;
			unsigned long MAN:2;
		} BIT;
	} SYRFL2R;
	union {
		unsigned long LONG;
		struct {
			unsigned long :19;
			unsigned long PDRQ:1;
			unsigned long :3;
			unsigned long DRQ:1;
			unsigned long :3;
			unsigned long SYNC:1;
			unsigned long :3;
			unsigned long ANCE:1;
		} BIT;
	} SYTRENR;
	char           wk5[4];
	unsigned long  MTCIDU;
	unsigned long  MTCIDL;
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long PNUM:16;
		} BIT;
	} MTPID;
	char           wk6[20];
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long DREQ:8;
			unsigned long SYNC:8;
			unsigned long ANCE:8;
		} BIT;
	} SYTLIR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long DRESP:8;
			unsigned long SYNC:8;
			unsigned long ANCE:8;
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
			unsigned long :8;
			unsigned long GMPR1:8;
			unsigned long :8;
			unsigned long GMPR2:8;
		} BIT;
	} GMPR;
	unsigned long  GMCQR;
	unsigned long  GMIDRU;
	unsigned long  GMIDRL;
	union {
		unsigned long LONG;
		struct {
			unsigned long CUTO:16;
			unsigned long :8;
			unsigned long TSRC:8;
		} BIT;
	} CUOTSR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long SRMV:16;
		} BIT;
	} SRR;
	char           wk8[8];
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long MACU:24;
		} BIT;
	} PPMACRU;
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long MACL:24;
		} BIT;
	} PPMACRL;
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long MACU:24;
		} BIT;
	} PDMACRU;
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long MACL:24;
		} BIT;
	} PDMACRL;
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long TYPE:16;
		} BIT;
	} PETYPER;
	char           wk9[12];
	unsigned long  PPIPR;
	unsigned long  PDIPR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :24;
			unsigned long EVTO:8;
		} BIT;
	} PETOSR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :24;
			unsigned long GETO:8;
		} BIT;
	} PGTOSR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :24;
			unsigned long PRTL:8;
		} BIT;
	} PPTTLR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :24;
			unsigned long PDTL:8;
		} BIT;
	} PDTTLR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long EVUPT:16;
		} BIT;
	} PEUDPR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long GEUPT:16;
		} BIT;
	} PGUDPR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :15;
			unsigned long EXTPRM:1;
			unsigned long :13;
			unsigned long ENB:1;
			unsigned long PRT:1;
			unsigned long SEL:1;
		} BIT;
	} FFLTR;
	char           wk10[28];
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long MACU:24;
		} BIT;
	} FMAC0RU;
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long MACL:24;
		} BIT;
	} FMAC0RL;
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long MACU:24;
		} BIT;
	} FMAC1RU;
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long MACL:24;
		} BIT;
	} FMAC1RL;
	char           wk11[80];
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long ASYMU:16;
		} BIT;
	} DASYMRU;
	unsigned long  DASYMRL;
	union {
		unsigned long LONG;
		struct {
			unsigned long INGP:16;
			unsigned long EGP:16;
		} BIT;
	} TSLATR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :11;
			unsigned long TCMOD:1;
			unsigned long :3;
			unsigned long FILDIS:1;
			unsigned long :3;
			unsigned long SBDIS:1;
			unsigned long :4;
			unsigned long TCYC:8;
		} BIT;
	} SYCONFR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :30;
			unsigned long FORM1:1;
			unsigned long FORM0:1;
		} BIT;
	} SYFORMR;
	unsigned long  RSTOUTR;
};

struct st_etherc {
	union {
		unsigned long LONG;
		struct {
			unsigned long :11;
			unsigned long TPC:1;
			unsigned long ZPF:1;
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
			unsigned char DACKSEL:1;
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
			unsigned char DACKSEL:1;
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
	char           wk0[2];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char FLWE:2;
		} BIT;
	} FWEPROR;
	char           wk1[7806329];
	union {
		unsigned char BYTE;
		struct {
			unsigned char CFAE:1;
			unsigned char :2;
			unsigned char CMDLK:1;
			unsigned char DFAE:1;
			unsigned char :2;
			unsigned char ECRCT:1;
		} BIT;
	} FASTAT;
	char           wk2[3];
	union {
		unsigned char BYTE;
		struct {
			unsigned char CFAEIE:1;
			unsigned char :2;
			unsigned char CMDLKIE:1;
			unsigned char DFAEIE:1;
			unsigned char :2;
			unsigned char ECRCTIE:1;
		} BIT;
	} FAEINT;
	char           wk3[3];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char FRDYIE:1;
		} BIT;
	} FRDYIE;
	char           wk4[23];
	union {
		unsigned long LONG;
		struct {
			unsigned long FSADDR:32;
		} BIT;
	} FSADDR;
	union {
		unsigned long LONG;
		struct {
			unsigned long FEADDR:32;
		} BIT;
	} FEADDR;
	char           wk5[28];
	union {
		unsigned short WORD;
		struct {
			unsigned short KEY:8;
			unsigned short :6;
			unsigned short FRAMTRAN:1;
			unsigned short FCRME:1;
		} BIT;
	} FCURAME;
	char           wk6[42];
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long FRDY:1;
			unsigned long ILGLERR:1;
			unsigned long ERSERR:1;
			unsigned long PRGERR:1;
			unsigned long SUSRDY:1;
			unsigned long DBFULL:1;
			unsigned long ERSSPD:1;
			unsigned long PRGSPD:1;
			unsigned long FCUERR:1;
			unsigned long FLWEERR:1;
			unsigned long :4;
			unsigned long FRDTCT:1;
			unsigned long FRCRCT:1;
		} BIT;
	} FSTATR;
	union {
		unsigned short WORD;
		struct {
			unsigned short KEY:8;
			unsigned short FENTRYD:1;
			unsigned short :6;
			unsigned short FENTRYC:1;
		} BIT;
	} FENTRYR;
	char           wk7[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short KEY:8;
			unsigned short :7;
			unsigned short FPROTCN:1;
		} BIT;
	} FPROTR;
	char           wk8[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short KEY:8;
			unsigned short :7;
			unsigned short SUINIT:1;
		} BIT;
	} FSUINITR;
	char           wk9[2];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char FLOCKST:1;
		} BIT;
	} FLKSTAT;
	char           wk10[15];
	union {
		unsigned short WORD;
		struct {
			unsigned short CMDR:8;
			unsigned short PCMDR:8;
		} BIT;
	} FCMDR;
	char           wk11[30];
	union {
		unsigned short WORD;
		struct {
			unsigned short :8;
			unsigned short PEERRST:8;
		} BIT;
	} FPESTAT;
	char           wk12[14];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char BCDIR:1;
		} BIT;
	} FBCCNT;
	char           wk13[3];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char BCST:1;
		} BIT;
	} FBCSTAT;
	char           wk14[3];
	union {
		unsigned long LONG;
		struct {
			unsigned long :13;
			unsigned long PSADR:19;
		} BIT;
	} FPSADDR;
	char           wk15[4];
	union {
		unsigned short WORD;
		struct {
			unsigned short :15;
			unsigned short ESUSPMD:1;
		} BIT;
	} FCPSR;
	char           wk16[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short KEY:8;
			unsigned short PCKA:8;
		} BIT;
	} FPCKAR;
};

struct st_gpt {
	union {
		unsigned short WORD;
		struct {
			unsigned short :12;
			unsigned short CST3:1;
			unsigned short CST2:1;
			unsigned short CST1:1;
			unsigned short CST0:1;
		} BIT;
	} GTSTR;
	union {
		unsigned short WORD;
		struct {
			unsigned short NFCS3:2;
			unsigned short NFCS2:2;
			unsigned short NFCS1:2;
			unsigned short NFCS0:2;
			unsigned short NFB3EN:1;
			unsigned short NFA3EN:1;
			unsigned short NFB2EN:1;
			unsigned short NFA2EN:1;
			unsigned short NFB1EN:1;
			unsigned short NFA1EN:1;
			unsigned short NFB0EN:1;
			unsigned short NFA0EN:1;
		} BIT;
	} NFCR;
	union {
		unsigned short WORD;
		struct {
			unsigned short CPHW3:2;
			unsigned short CPHW2:2;
			unsigned short CPHW1:2;
			unsigned short CPHW0:2;
			unsigned short CSHW3:2;
			unsigned short CSHW2:2;
			unsigned short CSHW1:2;
			unsigned short CSHW0:2;
		} BIT;
	} GTHSCR;
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short CCSW3:1;
			unsigned short CCSW2:1;
			unsigned short CCSW1:1;
			unsigned short CCSW0:1;
			unsigned short CCHW3:2;
			unsigned short CCHW2:2;
			unsigned short CCHW1:2;
			unsigned short CCHW0:2;
		} BIT;
	} GTHCCR;
	union {
		unsigned short WORD;
		struct {
			unsigned short CSHSL3:4;
			unsigned short CSHSL2:4;
			unsigned short CSHSL1:4;
			unsigned short CSHSL0:4;
		} BIT;
	} GTHSSR;
	union {
		unsigned short WORD;
		struct {
			unsigned short CSHPL3:4;
			unsigned short CSHPL2:4;
			unsigned short CSHPL1:4;
			unsigned short CSHPL0:4;
		} BIT;
	} GTHPSR;
	union {
		unsigned short WORD;
		struct {
			unsigned short :12;
			unsigned short WP3:1;
			unsigned short WP2:1;
			unsigned short WP1:1;
			unsigned short WP0:1;
		} BIT;
	} GTWP;
	union {
		unsigned short WORD;
		struct {
			unsigned short :2;
			unsigned short SYNC3:2;
			unsigned short :2;
			unsigned short SYNC2:2;
			unsigned short :2;
			unsigned short SYNC1:2;
			unsigned short :2;
			unsigned short SYNC0:2;
		} BIT;
	} GTSYNC;
	union {
		unsigned short WORD;
		struct {
			unsigned short GTETRGEN:1;
			unsigned short GTENFCS:2;
			unsigned short :11;
			unsigned short ETINEN:1;
			unsigned short ETIPEN:1;
		} BIT;
	} GTETINT;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short BD33:1;
			unsigned short BD32:1;
			unsigned short BD31:1;
			unsigned short BD30:1;
			unsigned short BD23:1;
			unsigned short BD22:1;
			unsigned short BD21:1;
			unsigned short BD20:1;
			unsigned short BD13:1;
			unsigned short BD12:1;
			unsigned short BD11:1;
			unsigned short BD10:1;
			unsigned short BD03:1;
			unsigned short BD02:1;
			unsigned short BD01:1;
			unsigned short BD00:1;
		} BIT;
	} GTBDR;
	char           wk1[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short :12;
			unsigned short SWP3:1;
			unsigned short SWP2:1;
			unsigned short SWP1:1;
			unsigned short SWP0:1;
		} BIT;
	} GTSWP;
};

struct st_gpt0 {
	union {
		unsigned short WORD;
		struct {
			unsigned short OBHLD:1;
			unsigned short OBDFLT:1;
			unsigned short GTIOB:6;
			unsigned short OAHLD:1;
			unsigned short OADFLT:1;
			unsigned short GTIOA:6;
		} BIT;
	} GTIOR;
	union {
		unsigned short WORD;
		struct {
			unsigned short ADTRBDEN:1;
			unsigned short ADTRBUEN:1;
			unsigned short ADTRADEN:1;
			unsigned short ADTRAUEN:1;
			unsigned short EINT:1;
			unsigned short :3;
			unsigned short GTINTPR:2;
			unsigned short GTINTF:1;
			unsigned short GTINTE:1;
			unsigned short GTINTD:1;
			unsigned short GTINTC:1;
			unsigned short GTINTB:1;
			unsigned short GTINTA:1;
		} BIT;
	} GTINTAD;
	union {
		unsigned short WORD;
		struct {
			unsigned short :2;
			unsigned short CCLR:2;
			unsigned short :2;
			unsigned short TPCS:2;
			unsigned short :5;
			unsigned short MD:3;
		} BIT;
	} GTCR;
	union {
		unsigned short WORD;
		struct {
			unsigned short :1;
			unsigned short ADTDB:1;
			unsigned short ADTTB:2;
			unsigned short :1;
			unsigned short ADTDA:1;
			unsigned short ADTTA:2;
			unsigned short :1;
			unsigned short CCRSWT:1;
			unsigned short PR:2;
			unsigned short CCRB:2;
			unsigned short CCRA:2;
		} BIT;
	} GTBER;
	union {
		unsigned short WORD;
		struct {
			unsigned short :14;
			unsigned short UDF:1;
			unsigned short UD:1;
		} BIT;
	} GTUDC;
	union {
		unsigned short WORD;
		struct {
			unsigned short :1;
			unsigned short ADTBL:1;
			unsigned short :1;
			unsigned short ADTAL:1;
			unsigned short :1;
			unsigned short IVTT:3;
			unsigned short IVTC:2;
			unsigned short ITLF:1;
			unsigned short ITLE:1;
			unsigned short ITLD:1;
			unsigned short ITLC:1;
			unsigned short ITLB:1;
			unsigned short ITLA:1;
		} BIT;
	} GTITC;
	union {
		unsigned short WORD;
		struct {
			unsigned short TUCF:1;
			unsigned short :3;
			unsigned short DTEF:1;
			unsigned short ITCNT:3;
		} BIT;
	} GTST;
	unsigned short GTCNT;
	unsigned short GTCCRA;
	unsigned short GTCCRB;
	unsigned short GTCCRC;
	unsigned short GTCCRD;
	unsigned short GTCCRE;
	unsigned short GTCCRF;
	unsigned short GTPR;
	unsigned short GTPBR;
	unsigned short GTPDBR;
	char           wk0[2];
	unsigned short GTADTRA;
	unsigned short GTADTBRA;
	unsigned short GTADTDBRA;
	char           wk1[2];
	unsigned short GTADTRB;
	unsigned short GTADTBRB;
	unsigned short GTADTDBRB;
	char           wk2[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short OBE:1;
			unsigned short OAE:1;
			unsigned short :1;
			unsigned short SWN:1;
			unsigned short :3;
			unsigned short NFV:1;
			unsigned short NFS:4;
			unsigned short NVB:1;
			unsigned short NVA:1;
			unsigned short NEB:1;
			unsigned short NEA:1;
		} BIT;
	} GTONCR;
	union {
		unsigned short WORD;
		struct {
			unsigned short :7;
			unsigned short TDFER:1;
			unsigned short :2;
			unsigned short TDBDE:1;
			unsigned short TDBUE:1;
			unsigned short :3;
			unsigned short TDE:1;
		} BIT;
	} GTDTCR;
	unsigned short GTDVU;
	unsigned short GTDVD;
	unsigned short GTDBU;
	unsigned short GTDBD;
	union {
		unsigned short WORD;
		struct {
			unsigned short :14;
			unsigned short SOS:2;
		} BIT;
	} GTSOS;
	union {
		unsigned short WORD;
		struct {
			unsigned short :15;
			unsigned short SOTR:1;
		} BIT;
	} GTSOTR;
};

struct st_icu {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char IR:1;
		} BIT;
	} IR[256];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DTCE:1;
		} BIT;
	} DTCER[256];
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
	char           wk0[192];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char SWINT:1;
		} BIT;
	} SWINTR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char SWINT2:1;
		} BIT;
	} SWINT2R;
	char           wk1[14];
	union {
		unsigned short WORD;
		struct {
			unsigned short FIEN:1;
			unsigned short :7;
			unsigned short FVCT:8;
		} BIT;
	} FIR;
	char           wk2[14];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char IPR:4;
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
			unsigned char :4;
			unsigned char IRQMD:2;
		} BIT;
	} IRQCR[16];
	char           wk11[16];
	union {
		unsigned char BYTE;
		struct {
			unsigned char FLTEN7:1;
			unsigned char FLTEN6:1;
			unsigned char FLTEN5:1;
			unsigned char FLTEN4:1;
			unsigned char FLTEN3:1;
			unsigned char FLTEN2:1;
			unsigned char FLTEN1:1;
			unsigned char FLTEN0:1;
		} BIT;
	} IRQFLTE0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char FLTEN15:1;
			unsigned char FLTEN14:1;
			unsigned char FLTEN13:1;
			unsigned char FLTEN12:1;
			unsigned char FLTEN11:1;
			unsigned char FLTEN10:1;
			unsigned char FLTEN9:1;
			unsigned char FLTEN8:1;
		} BIT;
	} IRQFLTE1;
	char           wk12[6];
	union {
		unsigned short WORD;
		struct {
			unsigned short FCLKSEL7:2;
			unsigned short FCLKSEL6:2;
			unsigned short FCLKSEL5:2;
			unsigned short FCLKSEL4:2;
			unsigned short FCLKSEL3:2;
			unsigned short FCLKSEL2:2;
			unsigned short FCLKSEL1:2;
			unsigned short FCLKSEL0:2;
		} BIT;
	} IRQFLTC0;
	union {
		unsigned short WORD;
		struct {
			unsigned short FCLKSEL15:2;
			unsigned short FCLKSEL14:2;
			unsigned short FCLKSEL13:2;
			unsigned short FCLKSEL12:2;
			unsigned short FCLKSEL11:2;
			unsigned short FCLKSEL10:2;
			unsigned short FCLKSEL9:2;
			unsigned short FCLKSEL8:2;
		} BIT;
	} IRQFLTC1;
	char           wk13[84];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ECCRAMST:1;
			unsigned char LVD2ST:1;
			unsigned char LVD1ST:1;
			unsigned char IWDTST:1;
			unsigned char WDTST:1;
			unsigned char OSTST:1;
			unsigned char NMIST:1;
		} BIT;
	} NMISR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ECCRAMEN:1;
			unsigned char LVD2EN:1;
			unsigned char LVD1EN:1;
			unsigned char IWDTEN:1;
			unsigned char WDTEN:1;
			unsigned char OSTEN:1;
			unsigned char NMIEN:1;
		} BIT;
	} NMIER;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char LVD2CLR:1;
			unsigned char LVD1CLR:1;
			unsigned char IWDTCLR:1;
			unsigned char WDTCLR:1;
			unsigned char OSTCLR:1;
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
	char           wk14[12];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char NFLTEN:1;
		} BIT;
	} NMIFLTE;
	char           wk15[3];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char NFCLKSEL:2;
		} BIT;
	} NMIFLTC;
	char           wk16[107];
	union {
		unsigned long LONG;
		struct {
			unsigned long IS31:1;
			unsigned long IS30:1;
			unsigned long IS29:1;
			unsigned long IS28:1;
			unsigned long IS27:1;
			unsigned long IS26:1;
			unsigned long IS25:1;
			unsigned long IS24:1;
			unsigned long IS23:1;
			unsigned long IS22:1;
			unsigned long IS21:1;
			unsigned long IS20:1;
			unsigned long IS19:1;
			unsigned long IS18:1;
			unsigned long IS17:1;
			unsigned long IS16:1;
			unsigned long IS15:1;
			unsigned long IS14:1;
			unsigned long IS13:1;
			unsigned long IS12:1;
			unsigned long IS11:1;
			unsigned long IS10:1;
			unsigned long IS9:1;
			unsigned long IS8:1;
			unsigned long IS7:1;
			unsigned long IS6:1;
			unsigned long IS5:1;
			unsigned long IS4:1;
			unsigned long IS3:1;
			unsigned long IS2:1;
			unsigned long IS1:1;
			unsigned long IS0:1;
		} BIT;
	} GRPBE0;
	char           wk17[44];
	union {
		unsigned long LONG;
		struct {
			unsigned long IS31:1;
			unsigned long IS30:1;
			unsigned long IS29:1;
			unsigned long IS28:1;
			unsigned long IS27:1;
			unsigned long IS26:1;
			unsigned long IS25:1;
			unsigned long IS24:1;
			unsigned long IS23:1;
			unsigned long IS22:1;
			unsigned long IS21:1;
			unsigned long IS20:1;
			unsigned long IS19:1;
			unsigned long IS18:1;
			unsigned long IS17:1;
			unsigned long IS16:1;
			unsigned long IS15:1;
			unsigned long IS14:1;
			unsigned long IS13:1;
			unsigned long IS12:1;
			unsigned long IS11:1;
			unsigned long IS10:1;
			unsigned long IS9:1;
			unsigned long IS8:1;
			unsigned long IS7:1;
			unsigned long IS6:1;
			unsigned long IS5:1;
			unsigned long IS4:1;
			unsigned long IS3:1;
			unsigned long IS2:1;
			unsigned long IS1:1;
			unsigned long IS0:1;
		} BIT;
	} GRPBL0;
	union {
		unsigned long LONG;
		struct {
			unsigned long IS31:1;
			unsigned long IS30:1;
			unsigned long IS29:1;
			unsigned long IS28:1;
			unsigned long IS27:1;
			unsigned long IS26:1;
			unsigned long IS25:1;
			unsigned long IS24:1;
			unsigned long IS23:1;
			unsigned long IS22:1;
			unsigned long IS21:1;
			unsigned long IS20:1;
			unsigned long IS19:1;
			unsigned long IS18:1;
			unsigned long IS17:1;
			unsigned long IS16:1;
			unsigned long IS15:1;
			unsigned long IS14:1;
			unsigned long IS13:1;
			unsigned long IS12:1;
			unsigned long IS11:1;
			unsigned long IS10:1;
			unsigned long IS9:1;
			unsigned long IS8:1;
			unsigned long IS7:1;
			unsigned long IS6:1;
			unsigned long IS5:1;
			unsigned long IS4:1;
			unsigned long IS3:1;
			unsigned long IS2:1;
			unsigned long IS1:1;
			unsigned long IS0:1;
		} BIT;
	} GRPBL1;
	char           wk18[8];
	union {
		unsigned long LONG;
		struct {
			unsigned long EN31:1;
			unsigned long EN30:1;
			unsigned long EN29:1;
			unsigned long EN28:1;
			unsigned long EN27:1;
			unsigned long EN26:1;
			unsigned long EN25:1;
			unsigned long EN24:1;
			unsigned long EN23:1;
			unsigned long EN22:1;
			unsigned long EN21:1;
			unsigned long EN20:1;
			unsigned long EN19:1;
			unsigned long EN18:1;
			unsigned long EN17:1;
			unsigned long EN16:1;
			unsigned long EN15:1;
			unsigned long EN14:1;
			unsigned long EN13:1;
			unsigned long EN12:1;
			unsigned long EN11:1;
			unsigned long EN10:1;
			unsigned long EN9:1;
			unsigned long EN8:1;
			unsigned long EN7:1;
			unsigned long EN6:1;
			unsigned long EN5:1;
			unsigned long EN4:1;
			unsigned long EN3:1;
			unsigned long EN2:1;
			unsigned long EN1:1;
			unsigned long EN0:1;
		} BIT;
	} GENBE0;
	char           wk19[44];
	union {
		unsigned long LONG;
		struct {
			unsigned long EN31:1;
			unsigned long EN30:1;
			unsigned long EN29:1;
			unsigned long EN28:1;
			unsigned long EN27:1;
			unsigned long EN26:1;
			unsigned long EN25:1;
			unsigned long EN24:1;
			unsigned long EN23:1;
			unsigned long EN22:1;
			unsigned long EN21:1;
			unsigned long EN20:1;
			unsigned long EN19:1;
			unsigned long EN18:1;
			unsigned long EN17:1;
			unsigned long EN16:1;
			unsigned long EN15:1;
			unsigned long EN14:1;
			unsigned long EN13:1;
			unsigned long EN12:1;
			unsigned long EN11:1;
			unsigned long EN10:1;
			unsigned long EN9:1;
			unsigned long EN8:1;
			unsigned long EN7:1;
			unsigned long EN6:1;
			unsigned long EN5:1;
			unsigned long EN4:1;
			unsigned long EN3:1;
			unsigned long EN2:1;
			unsigned long EN1:1;
			unsigned long EN0:1;
		} BIT;
	} GENBL0;
	union {
		unsigned long LONG;
		struct {
			unsigned long EN31:1;
			unsigned long EN30:1;
			unsigned long EN29:1;
			unsigned long EN28:1;
			unsigned long EN27:1;
			unsigned long EN26:1;
			unsigned long EN25:1;
			unsigned long EN24:1;
			unsigned long EN23:1;
			unsigned long EN22:1;
			unsigned long EN21:1;
			unsigned long EN20:1;
			unsigned long EN19:1;
			unsigned long EN18:1;
			unsigned long EN17:1;
			unsigned long EN16:1;
			unsigned long EN15:1;
			unsigned long EN14:1;
			unsigned long EN13:1;
			unsigned long EN12:1;
			unsigned long EN11:1;
			unsigned long EN10:1;
			unsigned long EN9:1;
			unsigned long EN8:1;
			unsigned long EN7:1;
			unsigned long EN6:1;
			unsigned long EN5:1;
			unsigned long EN4:1;
			unsigned long EN3:1;
			unsigned long EN2:1;
			unsigned long EN1:1;
			unsigned long EN0:1;
		} BIT;
	} GENBL1;
	char           wk20[8];
	union {
		unsigned long LONG;
		struct {
			unsigned long CLR31:1;
			unsigned long CLR30:1;
			unsigned long CLR29:1;
			unsigned long CLR28:1;
			unsigned long CLR27:1;
			unsigned long CLR26:1;
			unsigned long CLR25:1;
			unsigned long CLR24:1;
			unsigned long CLR23:1;
			unsigned long CLR22:1;
			unsigned long CLR21:1;
			unsigned long CLR20:1;
			unsigned long CLR19:1;
			unsigned long CLR18:1;
			unsigned long CLR17:1;
			unsigned long CLR16:1;
			unsigned long CLR15:1;
			unsigned long CLR14:1;
			unsigned long CLR13:1;
			unsigned long CLR12:1;
			unsigned long CLR11:1;
			unsigned long CLR10:1;
			unsigned long CLR9:1;
			unsigned long CLR8:1;
			unsigned long CLR7:1;
			unsigned long CLR6:1;
			unsigned long CLR5:1;
			unsigned long CLR4:1;
			unsigned long CLR3:1;
			unsigned long CLR2:1;
			unsigned long CLR1:1;
			unsigned long CLR0:1;
		} BIT;
	} GCRBE0;
	char           wk21[124];
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIBR0;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIBR1;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIBR2;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIBR3;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIBR4;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIBR5;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIBR6;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIBR7;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIBR8;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIBR9;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIBRA;
	char           wk22[117];
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBXR128;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBXR129;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBXR130;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBXR131;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBXR132;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBXR133;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBXR134;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBXR135;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBXR136;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBXR137;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBXR138;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBXR139;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBXR140;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBXR141;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBXR142;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBXR143;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR144;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR145;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR146;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR147;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR148;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR149;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR150;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR151;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR152;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR153;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR154;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR155;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR156;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR157;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR158;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR159;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR160;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR161;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR162;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR163;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR164;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR165;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR166;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR167;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR168;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR169;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR170;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR171;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR172;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR173;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR174;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR175;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR176;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR177;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR178;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR179;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR180;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR181;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR182;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR183;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR184;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR185;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR186;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR187;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR188;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR189;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR190;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR191;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR192;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR193;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR194;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR195;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR196;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR197;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR198;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR199;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR200;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR201;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR202;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR203;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR204;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR205;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR206;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIBR207;
	char           wk23[96];
	union {
		unsigned long LONG;
		struct {
			unsigned long IS31:1;
			unsigned long IS30:1;
			unsigned long IS29:1;
			unsigned long IS28:1;
			unsigned long IS27:1;
			unsigned long IS26:1;
			unsigned long IS25:1;
			unsigned long IS24:1;
			unsigned long IS23:1;
			unsigned long IS22:1;
			unsigned long IS21:1;
			unsigned long IS20:1;
			unsigned long IS19:1;
			unsigned long IS18:1;
			unsigned long IS17:1;
			unsigned long IS16:1;
			unsigned long IS15:1;
			unsigned long IS14:1;
			unsigned long IS13:1;
			unsigned long IS12:1;
			unsigned long IS11:1;
			unsigned long IS10:1;
			unsigned long IS9:1;
			unsigned long IS8:1;
			unsigned long IS7:1;
			unsigned long IS6:1;
			unsigned long IS5:1;
			unsigned long IS4:1;
			unsigned long IS3:1;
			unsigned long IS2:1;
			unsigned long IS1:1;
			unsigned long IS0:1;
		} BIT;
	} GRPAL0;
	union {
		unsigned long LONG;
		struct {
			unsigned long IS31:1;
			unsigned long IS30:1;
			unsigned long IS29:1;
			unsigned long IS28:1;
			unsigned long IS27:1;
			unsigned long IS26:1;
			unsigned long IS25:1;
			unsigned long IS24:1;
			unsigned long IS23:1;
			unsigned long IS22:1;
			unsigned long IS21:1;
			unsigned long IS20:1;
			unsigned long IS19:1;
			unsigned long IS18:1;
			unsigned long IS17:1;
			unsigned long IS16:1;
			unsigned long IS15:1;
			unsigned long IS14:1;
			unsigned long IS13:1;
			unsigned long IS12:1;
			unsigned long IS11:1;
			unsigned long IS10:1;
			unsigned long IS9:1;
			unsigned long IS8:1;
			unsigned long IS7:1;
			unsigned long IS6:1;
			unsigned long IS5:1;
			unsigned long IS4:1;
			unsigned long IS3:1;
			unsigned long IS2:1;
			unsigned long IS1:1;
			unsigned long IS0:1;
		} BIT;
	} GRPAL1;
	char           wk24[56];
	union {
		unsigned long LONG;
		struct {
			unsigned long EN31:1;
			unsigned long EN30:1;
			unsigned long EN29:1;
			unsigned long EN28:1;
			unsigned long EN27:1;
			unsigned long EN26:1;
			unsigned long EN25:1;
			unsigned long EN24:1;
			unsigned long EN23:1;
			unsigned long EN22:1;
			unsigned long EN21:1;
			unsigned long EN20:1;
			unsigned long EN19:1;
			unsigned long EN18:1;
			unsigned long EN17:1;
			unsigned long EN16:1;
			unsigned long EN15:1;
			unsigned long EN14:1;
			unsigned long EN13:1;
			unsigned long EN12:1;
			unsigned long EN11:1;
			unsigned long EN10:1;
			unsigned long EN9:1;
			unsigned long EN8:1;
			unsigned long EN7:1;
			unsigned long EN6:1;
			unsigned long EN5:1;
			unsigned long EN4:1;
			unsigned long EN3:1;
			unsigned long EN2:1;
			unsigned long EN1:1;
			unsigned long EN0:1;
		} BIT;
	} GENAL0;
	union {
		unsigned long LONG;
		struct {
			unsigned long EN31:1;
			unsigned long EN30:1;
			unsigned long EN29:1;
			unsigned long EN28:1;
			unsigned long EN27:1;
			unsigned long EN26:1;
			unsigned long EN25:1;
			unsigned long EN24:1;
			unsigned long EN23:1;
			unsigned long EN22:1;
			unsigned long EN21:1;
			unsigned long EN20:1;
			unsigned long EN19:1;
			unsigned long EN18:1;
			unsigned long EN17:1;
			unsigned long EN16:1;
			unsigned long EN15:1;
			unsigned long EN14:1;
			unsigned long EN13:1;
			unsigned long EN12:1;
			unsigned long EN11:1;
			unsigned long EN10:1;
			unsigned long EN9:1;
			unsigned long EN8:1;
			unsigned long EN7:1;
			unsigned long EN6:1;
			unsigned long EN5:1;
			unsigned long EN4:1;
			unsigned long EN3:1;
			unsigned long EN2:1;
			unsigned long EN1:1;
			unsigned long EN0:1;
		} BIT;
	} GENAL1;
	char           wk25[136];
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIAR0;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIAR1;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIAR2;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIAR3;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIAR4;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIAR5;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIAR6;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIAR7;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIAR8;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIAR9;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIARA;
	union {
		unsigned char BYTE;
//		struct {
//			unsigned char PIR7:1;
//			unsigned char PIR6:1;
//			unsigned char PIR5:1;
//			unsigned char PIR4:1;
//			unsigned char PIR3:1;
//			unsigned char PIR2:1;
//			unsigned char PIR1:1;
//			unsigned char PIR0:1;
//		} BIT;
	} PIARB;
	char           wk26[196];
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR208;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR209;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR210;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR211;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR212;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR213;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR214;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR215;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR216;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR217;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR218;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR219;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR220;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR221;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR222;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR223;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR224;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR225;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR226;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR227;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR228;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR229;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR230;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR231;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR232;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR233;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR234;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR235;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR236;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR237;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR238;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR239;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR240;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR241;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR242;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR243;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR244;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR245;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR246;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR247;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR248;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR249;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR250;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR251;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR252;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR253;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR254;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLI:8;
		} BIT;
	} SLIAR255;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char WPRC:1;
		} BIT;
	} SLIPRCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char SELEXD1:1;
			unsigned char SELEXD0:1;
		} BIT;
	} SELEXDR;
};

struct st_iwdt {
	unsigned char  IWDTRR;
	char           wk0[1];
	union {
		unsigned short WORD;
		struct {
			unsigned short :2;
			unsigned short RPSS:2;
			unsigned short :2;
			unsigned short RPES:2;
			unsigned short CKS:4;
			unsigned short :2;
			unsigned short TOPS:2;
		} BIT;
	} IWDTCR;
	union {
		unsigned short WORD;
		struct {
			unsigned short REFEF:1;
			unsigned short UNDFF:1;
			unsigned short CNTVAL:14;
		} BIT;
	} IWDTSR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char RSTIRQS:1;
		} BIT;
	} IWDTRCR;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char SLCSTP:1;
		} BIT;
	} IWDTCSTPR;
};

struct st_mmcif {
	union {
		unsigned long LONG;
//		struct {
//			unsigned long :1;
//			unsigned long BOOT:1;
//			unsigned long CMD:6;
//			unsigned long RTYP:2;
//			unsigned long RBSY:1;
//			unsigned long :1;
//			unsigned long WDAT:1;
//			unsigned long DWEN:1;
//			unsigned long CMLTE:1;
//			unsigned long CMD12EN:1;
//			unsigned long RIDXC:2;
//			unsigned long RCRC7C:2;
//			unsigned long :1;
//			unsigned long CRC16C:1;
//			unsigned long BOOTACK:1;
//			unsigned long CRCSTE:1;
//			unsigned long TBIT:1;
//			unsigned long OPDM:1;
//			unsigned long :2;
//			unsigned long SBIT:1;
//			unsigned long :1;
//			unsigned long DATW:2;
//		} BIT;
	} CECMDSET;
	char           wk0[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long ARG:32;
		} BIT;
	} CEARG;
	union {
		unsigned long LONG;
		struct {
			unsigned long C12ARG:32;
		} BIT;
	} CEARGCMD12;
	union {
		unsigned long LONG;
		struct {
			unsigned long :31;
			unsigned long BREAK:1;
		} BIT;
	} CECMDCTRL;
	union {
		unsigned long LONG;
		struct {
			unsigned long BLKCNT:16;
			unsigned long BLKSIZ:16;
		} BIT;
	} CEBLOCKSET;
	union {
		unsigned long LONG;
		struct {
			unsigned long MMCBUSBSY:1;
			unsigned long :6;
			unsigned long CLKEN:1;
			unsigned long :4;
			unsigned long CLKDIV:4;
			unsigned long :2;
			unsigned long SRSPTO:2;
			unsigned long SRBSYTO:4;
			unsigned long SRWDTO:4;
		} BIT;
	} CECLKCTRL;
	union {
		unsigned long LONG;
		struct {
			unsigned long :5;
			unsigned long DMATYP:1;
			unsigned long DMAWEN:1;
			unsigned long DMAREN:1;
			unsigned long :7;
			unsigned long ATYP:1;
		} BIT;
	} CEBUFACC;
	unsigned long  CERESP3;
	unsigned long  CERESP2;
	unsigned long  CERESP1;
	unsigned long  CERESP0;
	union {
		unsigned long LONG;
		struct {
			unsigned long RSP12:32;
		} BIT;
	} CERESPCMD12;
	union {
		unsigned long LONG;
//		struct {
//			unsigned long DATA:32;
//		} BIT;
	} CEDATA;
	char           wk1[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long SBTCLKDIV:4;
			unsigned long SBTACKTO:4;
			unsigned long SFSTBTDATTO:4;
			unsigned long SBTDATTO:4;
		} BIT;
	} CEBOOT;
	union {
		unsigned long LONG;
//		struct {
//			unsigned long :5;
//			unsigned long CMD12DRE:1;
//			unsigned long CMD12RBE:1;
//			unsigned long CMD12CRE:1;
//			unsigned long DTRANE:1;
//			unsigned long BUFRE:1;
//			unsigned long BUFWEN:1;
//			unsigned long BUFREN:1;
//			unsigned long :2;
//			unsigned long RBSYE:1;
//			unsigned long CRSPE:1;
//			unsigned long CMDVIO:1;
//			unsigned long BUFVIO:1;
//			unsigned long :2;
//			unsigned long WDATERR:1;
//			unsigned long RDATERR:1;
//			unsigned long RIDXERR:1;
//			unsigned long RSPERR:1;
//			unsigned long :3;
//			unsigned long CRCSTO:1;
//			unsigned long WDATTO:1;
//			unsigned long RDATTO:1;
//			unsigned long RBSYTO:1;
//			unsigned long RSPTO:1;
//		} BIT;
	} CEINT;
	union {
		unsigned long LONG;
		struct {
			unsigned long :5;
			unsigned long MCMD12DRE:1;
			unsigned long MCMD12RBE:1;
			unsigned long MCMD12CRE:1;
			unsigned long MDTRANE:1;
			unsigned long MBUFRE:1;
			unsigned long MBUFWEN:1;
			unsigned long MBUFREN:1;
			unsigned long :2;
			unsigned long MRBSYE:1;
			unsigned long MCRSPE:1;
			unsigned long MCMDVIO:1;
			unsigned long MBUFVIO:1;
			unsigned long :2;
			unsigned long MWDATERR:1;
			unsigned long MRDATERR:1;
			unsigned long MRIDXERR:1;
			unsigned long MRSPERR:1;
			unsigned long :3;
			unsigned long MCRCSTO:1;
			unsigned long MWDATTO:1;
			unsigned long MRDATTO:1;
			unsigned long MRBSYTO:1;
			unsigned long MRSPTO:1;
		} BIT;
	} CEINTEN;
	union {
		unsigned long LONG;
		struct {
			unsigned long CMDSEQ:1;
			unsigned long CMDSIG:1;
			unsigned long RSPIDX:6;
			unsigned long DATSIG:8;
			unsigned long RCVBLK:16;
		} BIT;
	} CEHOSTSTS1;
	union {
		unsigned long LONG;
		struct {
			unsigned long CRCSTE:1;
			unsigned long CRC16E:1;
			unsigned long AC12CRCE:1;
			unsigned long RSPCRC7E:1;
			unsigned long CRCSTEBE:1;
			unsigned long RDATEBE:1;
			unsigned long AC12REBE:1;
			unsigned long RSPEBE:1;
			unsigned long AC12IDXE:1;
			unsigned long RSPIDXE:1;
			unsigned long BTACKPATE:1;
			unsigned long BTACKEBE:1;
			unsigned long :1;
			unsigned long CRCST:3;
			unsigned long :1;
			unsigned long STRDATTO:1;
			unsigned long DATBSYTO:1;
			unsigned long CRCSTTO:1;
			unsigned long AC12BSYTO:1;
			unsigned long RSPBSYTO:1;
			unsigned long AC12RSPTO:1;
			unsigned long STRSPTO:1;
			unsigned long BTACKTO:1;
			unsigned long FSTBTDATTO:1;
			unsigned long BTDATTO:1;
		} BIT;
	} CEHOSTSTS2;
	char           wk2[32];
	union {
		unsigned long LONG;
//		struct {
//			unsigned long :17;
//			unsigned long CDSIG:1;
//			unsigned long CDRISE:1;
//			unsigned long CDFALL:1;
//			unsigned long :6;
//			unsigned long MCDRISE:1;
//			unsigned long MCDFALL:1;
//		} BIT;
	} CEDETECT;
	union {
		unsigned long LONG;
		struct {
			unsigned long :10;
			unsigned long RESNOUT:1;
			unsigned long :1;
			unsigned long CLKMAIN:1;
		} BIT;
	} CEADDMODE;
	char           wk3[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long SWRST:1;
			unsigned long :15;
			unsigned long VERSION:16;
		} BIT;
	} CEVERSION;
};

struct st_mpc {
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
	} PFCSE;
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char CS3S:2;
			unsigned char CS2S:2;
			unsigned char CS1S:2;
			unsigned char :1;
			unsigned char CS0S:1;
		} BIT;
	} PFCSS0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char CS7S:2;
			unsigned char CS6S:2;
			unsigned char CS5S:2;
			unsigned char CS4S:2;
		} BIT;
	} PFCSS1;
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
	} PFAOE0;
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
	} PFAOE1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char WR32BC32E:1;
			unsigned char WR1BC1E:1;
			unsigned char DH32E:1;
			unsigned char DHE:1;
			unsigned char BCLKO:1;
			unsigned char ADRHMS2:1;
			unsigned char ADRHMS:1;
			unsigned char ADRLE:1;
		} BIT;
	} PFBCR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SDCLKE:1;
			unsigned char DQM1E:1;
			unsigned char :1;
			unsigned char MDSDE:1;
			unsigned char ALES:1;
			unsigned char ALEOE:1;
			unsigned char WAITS:2;
		} BIT;
	} PFBCR1;
	char           wk1[6];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PHYMODE1:1;
			unsigned char PHYMODE0:1;
		} BIT;
	} PFENET;
	char           wk2[16];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B0WI:1;
			unsigned char PFSWE:1;
		} BIT;
	} PWPR;
	char           wk3[32];
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P00PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P01PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P02PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
		} BIT;
	} P03PFS;
	char           wk4[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
		} BIT;
	} P05PFS;
	char           wk5[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P07PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P10PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P11PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P12PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P13PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P14PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P15PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P16PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P17PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P20PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P21PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P22PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P23PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P24PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P25PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P26PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P27PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P30PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P31PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P32PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P33PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P34PFS;
	char           wk6[3];
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
		} BIT;
	} P40PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
		} BIT;
	} P41PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
		} BIT;
	} P42PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
		} BIT;
	} P43PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
		} BIT;
	} P44PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
		} BIT;
	} P45PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
		} BIT;
	} P46PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
		} BIT;
	} P47PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P50PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P51PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P52PFS;
	char           wk7[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P54PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P55PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P56PFS;
	char           wk8[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P60PFS;
	char           wk9[5];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P66PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} P67PFS;
	char           wk10[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P71PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P72PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P73PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P74PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P75PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P76PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P77PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P80PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P81PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P82PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P83PFS;
	char           wk11[2];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P86PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} P87PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char :1;
			unsigned char PSEL:6;
		} BIT;
	} P90PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char :1;
			unsigned char PSEL:6;
		} BIT;
	} P91PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char :1;
			unsigned char PSEL:6;
		} BIT;
	} P92PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char :1;
			unsigned char PSEL:6;
		} BIT;
	} P93PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char :1;
			unsigned char PSEL:6;
		} BIT;
	} P94PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char :1;
			unsigned char PSEL:6;
		} BIT;
	} P95PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char :1;
			unsigned char PSEL:6;
		} BIT;
	} P96PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char :1;
			unsigned char PSEL:6;
		} BIT;
	} P97PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PA0PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PA1PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PA2PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PA3PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PA4PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PA5PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PA6PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PA7PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PB0PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PB1PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PB2PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PB3PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PB4PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PB5PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PB6PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PB7PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PC0PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PC1PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PC2PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PC3PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PC4PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PC5PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PC6PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PC7PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PD0PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PD1PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PD2PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PD3PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PD4PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PD5PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PD6PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PD7PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char :1;
			unsigned char PSEL:6;
		} BIT;
	} PE0PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char :1;
			unsigned char PSEL:6;
		} BIT;
	} PE1PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PE2PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char :1;
			unsigned char PSEL:6;
		} BIT;
	} PE3PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char :1;
			unsigned char PSEL:6;
		} BIT;
	} PE4PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PE5PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PE6PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char ASEL:1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PE7PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PF0PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PF1PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PF2PFS;
	char           wk12[2];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char ISEL:1;
			unsigned char PSEL:6;
		} BIT;
	} PF5PFS;
	char           wk13[2];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PG0PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PG1PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PG2PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PG3PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PG4PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PG5PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PG6PFS;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PG7PFS;
	char           wk14[11];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PJ3PFS;
	char           wk15[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char PSEL:6;
		} BIT;
	} PJ5PFS;
};

struct st_mpu {
	union {
		unsigned long LONG;
		struct {
			unsigned long RSPN:28;
		} BIT;
	} RSPAGE0;
	union {
		unsigned long LONG;
		struct {
			unsigned long REPN:28;
			unsigned long UAC:3;
			unsigned long V:1;
		} BIT;
	} REPAGE0;
	union {
		unsigned long LONG;
		struct {
			unsigned long RSPN:28;
		} BIT;
	} RSPAGE1;
	union {
		unsigned long LONG;
		struct {
			unsigned long REPN:28;
			unsigned long UAC:3;
			unsigned long V:1;
		} BIT;
	} REPAGE1;
	union {
		unsigned long LONG;
		struct {
			unsigned long RSPN:28;
		} BIT;
	} RSPAGE2;
	union {
		unsigned long LONG;
		struct {
			unsigned long REPN:28;
			unsigned long UAC:3;
			unsigned long V:1;
		} BIT;
	} REPAGE2;
	union {
		unsigned long LONG;
		struct {
			unsigned long RSPN:28;
		} BIT;
	} RSPAGE3;
	union {
		unsigned long LONG;
		struct {
			unsigned long REPN:28;
			unsigned long UAC:3;
			unsigned long V:1;
		} BIT;
	} REPAGE3;
	union {
		unsigned long LONG;
		struct {
			unsigned long RSPN:28;
		} BIT;
	} RSPAGE4;
	union {
		unsigned long LONG;
		struct {
			unsigned long REPN:28;
			unsigned long UAC:3;
			unsigned long V:1;
		} BIT;
	} REPAGE4;
	union {
		unsigned long LONG;
		struct {
			unsigned long RSPN:28;
		} BIT;
	} RSPAGE5;
	union {
		unsigned long LONG;
		struct {
			unsigned long REPN:28;
			unsigned long UAC:3;
			unsigned long V:1;
		} BIT;
	} REPAGE5;
	union {
		unsigned long LONG;
		struct {
			unsigned long RSPN:28;
		} BIT;
	} RSPAGE6;
	union {
		unsigned long LONG;
		struct {
			unsigned long REPN:28;
			unsigned long UAC:3;
			unsigned long V:1;
		} BIT;
	} REPAGE6;
	union {
		unsigned long LONG;
		struct {
			unsigned long RSPN:28;
		} BIT;
	} RSPAGE7;
	union {
		unsigned long LONG;
		struct {
			unsigned long REPN:28;
			unsigned long UAC:3;
			unsigned long V:1;
		} BIT;
	} REPAGE7;
	char           wk0[192];
	union {
		unsigned long LONG;
		struct {
			unsigned long :31;
			unsigned long MPEN:1;
		} BIT;
	} MPEN;
	union {
		unsigned long LONG;
		struct {
			unsigned long :28;
			unsigned long UBAC:3;
		} BIT;
	} MPBAC;
	union {
		unsigned long LONG;
		struct {
			unsigned long :31;
			unsigned long CLR:1;
		} BIT;
	} MPECLR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :29;
			unsigned long DRW:1;
			unsigned long DMPER:1;
			unsigned long IMPER:1;
		} BIT;
	} MPESTS;
	char           wk1[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long DEA:32;
		} BIT;
	} MPDEA;
	char           wk2[8];
	union {
		unsigned long LONG;
		struct {
			unsigned long SA:32;
		} BIT;
	} MPSA;
	union {
		unsigned short WORD;
		struct {
			unsigned short :15;
			unsigned short S:1;
		} BIT;
	} MPOPS;
	union {
		unsigned short WORD;
		struct {
			unsigned short :15;
			unsigned short INV:1;
		} BIT;
	} MPOPI;
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long HITI:8;
			unsigned long :12;
			unsigned long UHACI:3;
		} BIT;
	} MHITI;
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long HITD:8;
			unsigned long :12;
			unsigned long UHACD:3;
		} BIT;
	} MHITD;
};

struct st_mtu {
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
	} TOERA;
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
	} TGCRA;
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
	} TOCR1A;
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
			unsigned char T3AEN:1;
			unsigned char T3ACOR:3;
			unsigned char T4VEN:1;
			unsigned char T4VCOR:3;
		} BIT;
	} TITCR1A;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char T3ACNT:3;
			unsigned char :1;
			unsigned char T4VCNT:3;
		} BIT;
	} TITCNT1A;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char BTE:2;
		} BIT;
	} TBTERA;
	char           wk4[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char TDER:1;
		} BIT;
	} TDERA;
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
	} TOLBRA;
	char           wk6[3];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char TITM:1;
		} BIT;
	} TITMRA;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char TRG4COR:3;
		} BIT;
	} TITCR2A;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char TRG4CNT:3;
		} BIT;
	} TITCNT2A;
	char           wk7[35];
	union {
		unsigned char BYTE;
		struct {
			unsigned char CCE:1;
			unsigned char :5;
			unsigned char SCC:1;
			unsigned char WRE:1;
		} BIT;
	} TWCRA;
	char           wk8[15];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DRS:1;
		} BIT;
	} TMDR2A;
	char           wk9[15];
	union {
		unsigned char BYTE;
		struct {
			unsigned char CST4:1;
			unsigned char CST3:1;
			unsigned char :2;
			unsigned char CST8:1;
			unsigned char CST2:1;
			unsigned char CST1:1;
			unsigned char CST0:1;
		} BIT;
	} TSTRA;
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
	} TSYRA;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SCH0:1;
			unsigned char SCH1:1;
			unsigned char SCH2:1;
			unsigned char SCH3:1;
			unsigned char SCH4:1;
			unsigned char :1;
			unsigned char SCH6:1;
			unsigned char SCH7:1;
		} BIT;
	} TCSYSTR;
	char           wk10[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char RWE:1;
		} BIT;
	} TRWERA;
	char           wk11[1925];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char OE7D:1;
			unsigned char OE7C:1;
			unsigned char OE6D:1;
			unsigned char OE7B:1;
			unsigned char OE7A:1;
			unsigned char OE6B:1;
		} BIT;
	} TOERB;
	char           wk12[3];
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
	} TOCR1B;
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
			unsigned char T6AEN:1;
			unsigned char T6ACOR:3;
			unsigned char T7VEN:1;
			unsigned char T7VCOR:3;
		} BIT;
	} TITCR1B;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char T6ACNT:3;
			unsigned char :1;
			unsigned char T7VCNT:3;
		} BIT;
	} TITCNT1B;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char BTE:2;
		} BIT;
	} TBTERB;
	char           wk16[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char TDER:1;
		} BIT;
	} TDERB;
	char           wk17[1];
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
	} TOLBRB;
	char           wk18[3];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char TITM:1;
		} BIT;
	} TITMRB;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char TRG7COR:3;
		} BIT;
	} TITCR2B;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char TRG7CNT:3;
		} BIT;
	} TITCNT2B;
	char           wk19[35];
	union {
		unsigned char BYTE;
		struct {
			unsigned char CCE:1;
			unsigned char :5;
			unsigned char SCC:1;
			unsigned char WRE:1;
		} BIT;
	} TWCRB;
	char           wk20[15];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DRS:1;
		} BIT;
	} TMDR2B;
	char           wk21[15];
	union {
		unsigned char BYTE;
		struct {
			unsigned char CST7:1;
			unsigned char CST6:1;
		} BIT;
	} TSTRB;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SYNC7:1;
			unsigned char SYNC6:1;
		} BIT;
	} TSYRB;
	char           wk22[2];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char RWE:1;
		} BIT;
	} TRWERB;
};

struct st_mtu0 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char NFCS:2;
			unsigned char NFDEN:1;
			unsigned char NFCEN:1;
			unsigned char NFBEN:1;
			unsigned char NFAEN:1;
		} BIT;
	} NFCR0;
	char           wk0[8];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char NFCS:2;
			unsigned char NFDEN:1;
			unsigned char NFCEN:1;
			unsigned char NFBEN:1;
			unsigned char NFAEN:1;
		} BIT;
	} NFCRC;
	char           wk1[102];
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
	} TMDR1;
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
			unsigned char TTGE2:1;
			unsigned char :5;
			unsigned char TGIEF:1;
			unsigned char TGIEE:1;
		} BIT;
	} TIER2;
	char           wk4[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char TTSE:1;
			unsigned char TTSB:1;
			unsigned char TTSA:1;
		} BIT;
	} TBTM;
	char           wk5[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char TPSC2:3;
		} BIT;
	} TCR2;
};

struct st_mtu1 {
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char NFCS:2;
			unsigned char NFDEN:1;
			unsigned char NFCEN:1;
			unsigned char NFBEN:1;
			unsigned char NFAEN:1;
		} BIT;
	} NFCR1;
	char           wk1[238];
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
	} TMDR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char IOB:4;
			unsigned char IOA:4;
		} BIT;
	} TIOR;
	char           wk2[1];
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
	char           wk3[4];
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
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char PHCKSEL:1;
			unsigned char LWA:1;
		} BIT;
	} TMDR3;
	char           wk4[2];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char PCB:2;
			unsigned char TPSC2:3;
		} BIT;
	} TCR2;
	char           wk5[11];
	unsigned long  TCNTLW;
	unsigned long  TGRALW;
	unsigned long  TGRBLW;
};

struct st_mtu2 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char NFCS:2;
			unsigned char NFDEN:1;
			unsigned char NFCEN:1;
			unsigned char NFBEN:1;
			unsigned char NFAEN:1;
		} BIT;
	} NFCR2;
	char           wk0[365];
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
	} TMDR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char IOB:4;
			unsigned char IOA:4;
		} BIT;
	} TIOR;
	char           wk1[1];
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
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char PCB:2;
			unsigned char TPSC2:3;
		} BIT;
	} TCR2;
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
	} TMDR1;
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
	char           wk8[19];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char TPSC2:3;
		} BIT;
	} TCR2;
	char           wk9[37];
	unsigned short TGRE;
	char           wk10[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char NFCS:2;
			unsigned char NFDEN:1;
			unsigned char NFCEN:1;
			unsigned char NFBEN:1;
			unsigned char NFAEN:1;
		} BIT;
	} NFCR3;
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
	} TMDR1;
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
	char           wk11[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char TPSC2:3;
		} BIT;
	} TCR2;
	char           wk12[38];
	unsigned short TGRE;
	unsigned short TGRF;
	char           wk13[28];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char NFCS:2;
			unsigned char NFDEN:1;
			unsigned char NFCEN:1;
			unsigned char NFBEN:1;
			unsigned char NFAEN:1;
		} BIT;
	} NFCR4;
};

struct st_mtu5 {
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char NFCS:2;
			unsigned char :1;
			unsigned char NFWEN:1;
			unsigned char NFVEN:1;
			unsigned char NFUEN:1;
		} BIT;
	} NFCR5;
	char           wk1[490];
	unsigned short TCNTU;
	unsigned short TGRU;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char TPSC:2;
		} BIT;
	} TCRU;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char CKEG:2;
			unsigned char TPSC2:3;
		} BIT;
	} TCR2U;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char IOC:5;
		} BIT;
	} TIORU;
	char           wk2[9];
	unsigned short TCNTV;
	unsigned short TGRV;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char TPSC:2;
		} BIT;
	} TCRV;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char CKEG:2;
			unsigned char TPSC2:3;
		} BIT;
	} TCR2V;
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
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char CKEG:2;
			unsigned char TPSC2:3;
		} BIT;
	} TCR2W;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char IOC:5;
		} BIT;
	} TIORW;
	char           wk4[11];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char TGIE5U:1;
			unsigned char TGIE5V:1;
			unsigned char TGIE5W:1;
		} BIT;
	} TIER;
	char           wk5[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char CSTU5:1;
			unsigned char CSTV5:1;
			unsigned char CSTW5:1;
		} BIT;
	} TSTR;
	char           wk6[1];
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

struct st_mtu6 {
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
	} TMDR1;
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
	char           wk8[19];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char TPSC2:3;
		} BIT;
	} TCR2;
	char           wk9[3];
	union {
		unsigned char BYTE;
		struct {
			unsigned char CE0A:1;
			unsigned char CE0B:1;
			unsigned char CE0C:1;
			unsigned char CE0D:1;
			unsigned char CE1A:1;
			unsigned char CE1B:1;
			unsigned char CE2A:1;
			unsigned char CE2B:1;
		} BIT;
	} TSYCR;
	char           wk10[33];
	unsigned short TGRE;
	char           wk11[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char NFCS:2;
			unsigned char NFDEN:1;
			unsigned char NFCEN:1;
			unsigned char NFBEN:1;
			unsigned char NFAEN:1;
		} BIT;
	} NFCR6;
};

struct st_mtu7 {
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
	} TMDR1;
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
			unsigned short UT7AE:1;
			unsigned short DT7AE:1;
			unsigned short UT7BE:1;
			unsigned short DT7BE:1;
			unsigned short ITA6AE:1;
			unsigned short ITA7VE:1;
			unsigned short ITB6AE:1;
			unsigned short ITB7VE:1;
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
			unsigned char :5;
			unsigned char TPSC2:3;
		} BIT;
	} TCR2;
	char           wk12[38];
	unsigned short TGRE;
	unsigned short TGRF;
	char           wk13[28];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char NFCS:2;
			unsigned char NFDEN:1;
			unsigned char NFCEN:1;
			unsigned char NFBEN:1;
			unsigned char NFAEN:1;
		} BIT;
	} NFCR7;
};

struct st_mtu8 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char NFCS:2;
			unsigned char NFDEN:1;
			unsigned char NFCEN:1;
			unsigned char NFBEN:1;
			unsigned char NFAEN:1;
		} BIT;
	} NFCR8;
	char           wk0[871];
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
			unsigned char :2;
			unsigned char BFB:1;
			unsigned char BFA:1;
			unsigned char MD:4;
		} BIT;
	} TMDR1;
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
			unsigned char :3;
			unsigned char TCIEV:1;
			unsigned char TGIED:1;
			unsigned char TGIEC:1;
			unsigned char TGIEB:1;
			unsigned char TGIEA:1;
		} BIT;
	} TIER;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char TPSC2:3;
		} BIT;
	} TCR2;
	char           wk2[1];
	unsigned long  TCNT;
	unsigned long  TGRA;
	unsigned long  TGRB;
	unsigned long  TGRC;
	unsigned long  TGRD;
};

struct st_pdc {
	union {
		unsigned long LONG;
		struct {
			unsigned long :17;
			unsigned long EDS:1;
			unsigned long PCKDIV:3;
			unsigned long PCKOE:1;
			unsigned long HERIE:1;
			unsigned long VERIE:1;
			unsigned long UDRIE:1;
			unsigned long OVIE:1;
			unsigned long FEIE:1;
			unsigned long DFIE:1;
			unsigned long PRST:1;
			unsigned long HPS:1;
			unsigned long VPS:1;
			unsigned long PCKE:1;
		} BIT;
	} PCCR0;
	union {
		unsigned long LONG;
		struct {
			unsigned long :31;
			unsigned long PCE:1;
		} BIT;
	} PCCR1;
	union {
		unsigned long LONG;
		struct {
			unsigned long :25;
			unsigned long HERF:1;
			unsigned long VERF:1;
			unsigned long UDRF:1;
			unsigned long OVRF:1;
			unsigned long FEF:1;
			unsigned long FEMPF:1;
			unsigned long FBSY:1;
		} BIT;
	} PCSR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :30;
			unsigned long HSYNC:1;
			unsigned long VSYNC:1;
		} BIT;
	} PCMONR;
	union {
		unsigned long LONG;
	} PCDR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :4;
			unsigned long VSZ:12;
			unsigned long :4;
			unsigned long VST:12;
		} BIT;
	} VCR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :4;
			unsigned long HSZ:12;
			unsigned long :4;
			unsigned long HST:12;
		} BIT;
	} HCR;
};

struct st_poe {
	union {
		unsigned short WORD;
		struct {
			unsigned short :3;
			unsigned short POE0F:1;
			unsigned short :3;
			unsigned short PIE1:1;
			unsigned short :6;
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
			unsigned short :3;
			unsigned short POE4F:1;
			unsigned short :3;
			unsigned short PIE2:1;
			unsigned short :6;
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
			unsigned char :3;
			unsigned char GPT23HIZ:1;
			unsigned char GPT01HIZ:1;
			unsigned char MTUCH0HIZ:1;
			unsigned char MTUCH67HIZ:1;
			unsigned char MTUCH34HIZ:1;
		} BIT;
	} SPOER;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char MTU0DZE:1;
			unsigned char MTU0CZE:1;
			unsigned char MTU0BZE:1;
			unsigned char MTU0AZE:1;
		} BIT;
	} POECR1;
	union {
		unsigned short WORD;
		struct {
			unsigned short :5;
			unsigned short MTU3BDZE:1;
			unsigned short MTU4ACZE:1;
			unsigned short MTU4BDZE:1;
			unsigned short :5;
			unsigned short MTU6BDZE:1;
			unsigned short MTU7ACZE:1;
			unsigned short MTU7BDZE:1;
		} BIT;
	} POECR2;
	union {
		unsigned short WORD;
		struct {
			unsigned short :6;
			unsigned short GPT3ABZE:1;
			unsigned short GPT2ABZE:1;
			unsigned short :6;
			unsigned short GPT1ABZE:1;
			unsigned short GPT0ABZE:1;
		} BIT;
	} POECR3;
	union {
		unsigned short WORD;
		struct {
			unsigned short :2;
			unsigned short IC5ADDMT67ZE:1;
			unsigned short IC4ADDMT67ZE:1;
			unsigned short IC3ADDMT67ZE:1;
			unsigned short :1;
			unsigned short IC1ADDMT67ZE:1;
			unsigned short :3;
			unsigned short IC5ADDMT34ZE:1;
			unsigned short IC4ADDMT34ZE:1;
			unsigned short IC3ADDMT34ZE:1;
			unsigned short IC2ADDMT34ZE:1;
		} BIT;
	} POECR4;
	union {
		unsigned short WORD;
		struct {
			unsigned short :10;
			unsigned short IC5ADDMT0ZE:1;
			unsigned short IC4ADDMT0ZE:1;
			unsigned short :1;
			unsigned short IC2ADDMT0ZE:1;
			unsigned short IC1ADDMT0ZE:1;
		} BIT;
	} POECR5;
	union {
		unsigned short WORD;
		struct {
			unsigned short :3;
			unsigned short IC4ADDGPT23ZE:1;
			unsigned short IC3ADDGPT23ZE:1;
			unsigned short IC2ADDGPT23ZE:1;
			unsigned short IC1ADDGPT23ZE:1;
			unsigned short :3;
			unsigned short IC5ADDGPT01ZE:1;
			unsigned short :1;
			unsigned short IC3ADDGPT01ZE:1;
			unsigned short IC2ADDGPT01ZE:1;
			unsigned short IC1ADDGPT01ZE:1;
		} BIT;
	} POECR6;
	union {
		unsigned short WORD;
		struct {
			unsigned short :3;
			unsigned short POE10F:1;
			unsigned short :2;
			unsigned short POE10E:1;
			unsigned short PIE4:1;
			unsigned short :6;
			unsigned short POE10M:2;
		} BIT;
	} ICSR4;
	union {
		unsigned short WORD;
		struct {
			unsigned short :3;
			unsigned short POE11F:1;
			unsigned short :2;
			unsigned short POE11E:1;
			unsigned short PIE5:1;
			unsigned short :6;
			unsigned short POE11M:2;
		} BIT;
	} ICSR5;
	union {
		unsigned short WORD;
		struct {
			unsigned short :8;
			unsigned short OLSEN:1;
			unsigned short :1;
			unsigned short OLSG2B:1;
			unsigned short OLSG2A:1;
			unsigned short OLSG1B:1;
			unsigned short OLSG1A:1;
			unsigned short OLSG0B:1;
			unsigned short OLSG0A:1;
		} BIT;
	} ALR1;
	union {
		unsigned short WORD;
		struct {
			unsigned short :3;
			unsigned short OSTSTF:1;
			unsigned short :2;
			unsigned short OSTSTE:1;
		} BIT;
	} ICSR6;
	char           wk0[2];
	union {
		unsigned char BYTE;
		struct {
			unsigned char G0BSEL:4;
			unsigned char G0ASEL:4;
		} BIT;
	} G0SELR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char G1BSEL:4;
			unsigned char G1ASEL:4;
		} BIT;
	} G1SELR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char G2BSEL:4;
			unsigned char G2ASEL:4;
		} BIT;
	} G2SELR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char G3BSEL:4;
			unsigned char G3ASEL:4;
		} BIT;
	} G3SELR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char M0BSEL:4;
			unsigned char M0ASEL:4;
		} BIT;
	} M0SELR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char M0DSEL:4;
			unsigned char M0CSEL:4;
		} BIT;
	} M0SELR2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char M3DSEL:4;
			unsigned char M3BSEL:4;
		} BIT;
	} M3SELR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char M4CSEL:4;
			unsigned char M4ASEL:4;
		} BIT;
	} M4SELR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char M4DSEL:4;
			unsigned char M4BSEL:4;
		} BIT;
	} M4SELR2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char M4G2SEL:1;
			unsigned char M4G1SEL:1;
			unsigned char M3G0SEL:1;
		} BIT;
	} MGSELR;
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
	} PDR;
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
	} PODR;
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
	} PIDR;
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
	} PMR;
	char           wk3[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :3;
			unsigned char B2:1;
		} BIT;
	} ODR1;
	char           wk4[62];
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
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DSCR;
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
	} PDR;
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
	} PODR;
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
	} PIDR;
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
	} PMR;
	char           wk3[32];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR1;
	char           wk4[61];
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
	} PDR;
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
	} PODR;
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
	} PIDR;
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
	} PMR;
	char           wk3[33];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR1;
	char           wk4[60];
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
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
		} BIT;
	} DSCR;
};

struct st_port3 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PODR;
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
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PMR;
	char           wk3[34];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :3;
			unsigned char B0:1;
		} BIT;
	} ODR1;
	char           wk4[59];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PCR;
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
	} PDR;
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
	} PODR;
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
	} PIDR;
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
	} PMR;
	char           wk3[35];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR1;
	char           wk4[58];
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

struct st_port5 {
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
	} PDR;
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
	} PODR;
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
	} PIDR;
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
	} PMR;
	char           wk3[36];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR1;
	char           wk4[57];
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
	} PCR;
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :3;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DSCR;
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
	} PDR;
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
	} PODR;
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
	} PIDR;
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
	} PMR;
	char           wk3[37];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR1;
	char           wk4[56];
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
	} PDR;
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
	} PODR;
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
	} PIDR;
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
	} PMR;
	char           wk3[38];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR1;
	char           wk4[55];
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

struct st_port8 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char :2;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char :2;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char :2;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char :2;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PMR;
	char           wk3[39];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
		} BIT;
	} ODR1;
	char           wk4[54];
	union {
		unsigned char BYTE;
		struct {
			unsigned char B7:1;
			unsigned char B6:1;
			unsigned char :2;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PCR;
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
	} PDR;
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
	} PODR;
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
	} PIDR;
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
	} PMR;
	char           wk3[40];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR1;
	char           wk4[53];
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
	char           wk5[31];
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
	} DSCR;
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
	} PDR;
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
	} PODR;
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
	} PIDR;
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
	} PMR;
	char           wk3[41];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR1;
	char           wk4[52];
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
	char           wk5[31];
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
	} DSCR;
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
	} PDR;
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
	} PODR;
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
	} PIDR;
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
	} PMR;
	char           wk3[42];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR1;
	char           wk4[51];
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
	char           wk5[31];
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
	} DSCR;
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
	} PDR;
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
	} PODR;
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
	} PIDR;
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
	} PMR;
	char           wk3[43];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR1;
	char           wk4[50];
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
	char           wk5[31];
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
	} DSCR;
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
	} PDR;
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
	} PODR;
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
	} PIDR;
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
	} PMR;
	char           wk3[44];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR1;
	char           wk4[49];
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
	char           wk5[31];
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
	} DSCR;
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
	} PDR;
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
	} PODR;
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
	} PIDR;
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
	} PMR;
	char           wk3[45];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR1;
	char           wk4[48];
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
	char           wk5[31];
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
	} DSCR;
};

struct st_portf {
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
	} PDR;
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
	} PODR;
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
	} PIDR;
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
	} PMR;
	char           wk3[46];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR1;
	char           wk4[47];
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
	} PCR;
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
	} PDR;
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
	} PODR;
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
	} PIDR;
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
	} PMR;
	char           wk3[47];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
			unsigned char :1;
			unsigned char B4:1;
			unsigned char :1;
			unsigned char B2:1;
			unsigned char :1;
			unsigned char B0:1;
		} BIT;
	} ODR1;
	char           wk4[46];
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
	char           wk5[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DSCR;
};

struct st_portj {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char B5:1;
			unsigned char :1;
			unsigned char B3:1;
		} BIT;
	} PDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char B5:1;
			unsigned char :1;
			unsigned char B3:1;
		} BIT;
	} PODR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char B5:1;
			unsigned char :1;
			unsigned char B3:1;
		} BIT;
	} PIDR;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char B5:1;
			unsigned char :1;
			unsigned char B3:1;
		} BIT;
	} PMR;
	char           wk3[49];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char B6:1;
		} BIT;
	} ODR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char B2:1;
		} BIT;
	} ODR1;
	char           wk4[44];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char B5:1;
			unsigned char :1;
			unsigned char B3:1;
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

struct st_ptpedmac {
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
	unsigned long  TDLAR;
	char           wk3[4];
	unsigned long  RDLAR;
	char           wk4[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :1;
			unsigned long TWB:1;
			unsigned long :3;
			unsigned long TABT:1;
			unsigned long :1;
			unsigned long RFCOF:1;
			unsigned long ADE:1;
			unsigned long :1;
			unsigned long TC:1;
			unsigned long TDE:1;
			unsigned long TFUF:1;
			unsigned long FR:1;
			unsigned long RDE:1;
			unsigned long RFOF:1;
			unsigned long :7;
			unsigned long MACE:1;
			unsigned long RPORT:1;
			unsigned long :2;
			unsigned long PVER:1;
			unsigned long TYPE:4;
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
			unsigned long :1;
			unsigned long RFCOFIP:1;
			unsigned long ADEIP:1;
			unsigned long :1;
			unsigned long TCIP:1;
			unsigned long TDEIP:1;
			unsigned long TFUFIP:1;
			unsigned long FRIP:1;
			unsigned long RDEIP:1;
			unsigned long RFOFIP:1;
			unsigned long :7;
			unsigned long MACEIP:1;
			unsigned long RPORTIP:1;
			unsigned long :2;
			unsigned long PVERIP:1;
		} BIT;
	} EESIPR;
	char           wk6[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :24;
			unsigned long RPORTCE:1;
			unsigned long :2;
			unsigned long PVERCE:1;
			unsigned long TYPECE:4;
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
			unsigned long :31;
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
			unsigned long ELB:1;
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
	unsigned long  RBWAR;
	unsigned long  RDFAR;
	char           wk14[4];
	unsigned long  TBRAR;
	unsigned long  TDFAR;
};

struct st_qspi {
	union {
		unsigned char BYTE;
		struct {
			unsigned char SPRIE:1;
			unsigned char SPE:1;
			unsigned char SPTIE:1;
			unsigned char :1;
			unsigned char MSTR:1;
			unsigned char :1;
			unsigned char SPSSLIE:1;
		} BIT;
	} SPCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char SSLP:1;
		} BIT;
	} SSLP;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char MOIFE:1;
			unsigned char MOIFV:1;
			unsigned char :1;
			unsigned char IO3FV:1;
			unsigned char IO2FV:1;
			unsigned char SPLP:1;
		} BIT;
	} SPPCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SPRFF:1;
			unsigned char TREND:1;
			unsigned char SPTEF:1;
			unsigned char SPSSLF:1;
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
			unsigned char :6;
			unsigned char SPSC:2;
		} BIT;
	} SPSCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char SPSS:2;
		} BIT;
	} SPSSR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SPBR7:1;
			unsigned char SPBR6:1;
			unsigned char SPBR5:1;
			unsigned char SPBR4:1;
			unsigned char SPBR3:1;
			unsigned char SPBR2:1;
			unsigned char SPBR1:1;
			unsigned char SPBR0:1;
		} BIT;
	} SPBR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char TXDMY:1;
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
	char           wk0[1];
	union {
		unsigned short WORD;
		struct {
			unsigned short SCKDEN:1;
			unsigned short SLNDEN:1;
			unsigned short SPNDEN:1;
			unsigned short LSBF:1;
			unsigned short SPB:4;
			unsigned short SSLKP:1;
			unsigned short SPIMOD:2;
			unsigned short SPRW:1;
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
			unsigned short SPIMOD:2;
			unsigned short SPRW:1;
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
			unsigned short SPIMOD:2;
			unsigned short SPRW:1;
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
			unsigned short SPIMOD:2;
			unsigned short SPRW:1;
			unsigned short BRDV:2;
			unsigned short CPOL:1;
			unsigned short CPHA:1;
		} BIT;
	} SPCMD3;
	union {
		unsigned char BYTE;
		struct {
			unsigned char TXRST:1;
			unsigned char RXRST:1;
			unsigned char TXTRG:2;
			unsigned char TXTRGEX:1;
			unsigned char RXTRG:3;
		} BIT;
	} SPBFCR;
	char           wk1[1];
	union {
		unsigned short WORD;
		struct {
			unsigned short :2;
			unsigned short TXBC:6;
			unsigned short :2;
			unsigned short RXBC:6;
		} BIT;
	} SPBDCR;
	unsigned long SPBMUL0;
	unsigned long SPBMUL1;
	unsigned long SPBMUL2;
	unsigned long SPBMUL3;
};

struct st_ram {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char RAMMODE:2;
		} BIT;
	} RAMMODE;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char RAMERR:1;
		} BIT;
	} RAMSTS;
	char           wk0[2];
	union {
		unsigned char BYTE;
		struct {
			unsigned char KW:7;
			unsigned char RAMPRCR:1;
		} BIT;
	} RAMPRCR;
	char           wk1[3];
	union {
		unsigned long LONG;
		struct {
			unsigned long :13;
			unsigned long READ:16;
			unsigned long :3;
		} BIT;
	} RAMECAD;
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
			unsigned char SSL3P:1;
			unsigned char SSL2P:1;
			unsigned char SSL1P:1;
			unsigned char SSL0P:1;
		} BIT;
	} SSLP;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char MOIFE:1;
			unsigned char MOIFV:1;
			unsigned char :2;
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
	unsigned char SPBR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char SPLW:1;
			unsigned char SPRDTD:1;
			unsigned char :2;
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
			unsigned char :3;
			unsigned char SCKASE:1;
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
			unsigned char :1;
			unsigned char F1HZ:1;
			unsigned char F2HZ:1;
			unsigned char F4HZ:1;
			unsigned char F8HZ:1;
			unsigned char F16HZ:1;
			unsigned char F32HZ:1;
			unsigned char F64HZ:1;
		} BIT;
	} R64CNT;
	char           wk0[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char :1;
				unsigned char SEC10:3;
				unsigned char SEC1:4;
			} BIT;
		} RSECCNT;
		union {
			unsigned char BYTE;
			struct {
				unsigned char BCNT:8;
			} BIT;
		} BCNT0;
	};
	char           wk1[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char :1;
				unsigned char MIN10:3;
				unsigned char MIN1:4;
			} BIT;
		} RMINCNT;
		union {
			unsigned char BYTE;
			struct {
				unsigned char BCNT:8;
			} BIT;
		} BCNT1;
	};
	char           wk2[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char :1;
				unsigned char PM:1;
				unsigned char HR10:2;
				unsigned char HR1:4;
			} BIT;
		} RHRCNT;
		union {
			unsigned char BYTE;
			struct {
				unsigned char BCNT:8;
			} BIT;
		} BCNT2;
	};
	char           wk3[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char :5;
				unsigned char DAYW:3;
			} BIT;
		} RWKCNT;
		union {
			unsigned char BYTE;
			struct {
				unsigned char BCNT:8;
			} BIT;
		} BCNT3;
	};
	char           wk4[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char DATE10:2;
			unsigned char DATE1:4;
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
			unsigned short :8;
			unsigned short YR10:4;
			unsigned short YR1:4;
		} BIT;
	} RYRCNT;
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char ENB:1;
				unsigned char SEC10:3;
				unsigned char SEC1:4;
			} BIT;
		} RSECAR;
		union {
			unsigned char BYTE;
			struct {
				unsigned char BCNTAR:8;
			} BIT;
		} BCNT0AR;
	};
	char           wk7[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char ENB:1;
				unsigned char MIN10:3;
				unsigned char MIN1:4;
			} BIT;
		} RMINAR;
		union {
			unsigned char BYTE;
			struct {
				unsigned char BCNTAR:8;
			} BIT;
		} BCNT1AR;
	};
	char           wk8[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char ENB:1;
				unsigned char PM:1;
				unsigned char HR10:2;
				unsigned char HR1:4;
			} BIT;
		} RHRAR;
		union {
			unsigned char BYTE;
			struct {
				unsigned char BCNTAR:8;
			} BIT;
		} BCNT2AR;
	};
	char           wk9[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char ENB:1;
				unsigned char :4;
				unsigned char DAYW:3;
			} BIT;
		} RWKAR;
		union {
			unsigned char BYTE;
			struct {
				unsigned char BCNTAR:8;
			} BIT;
		} BCNT3AR;
	};
	char           wk10[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char ENB:1;
				unsigned char :1;
				unsigned char DATE10:2;
				unsigned char DATE1:4;
			} BIT;
		} RDAYAR;
		union {
			unsigned char BYTE;
			struct {
				unsigned char ENB:8;
			} BIT;
		} BCNT0AER;
	};
	char           wk11[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char ENB:1;
				unsigned char :2;
				unsigned char MON10:1;
				unsigned char MON1:4;
			} BIT;
		} RMONAR;
		union {
			unsigned char BYTE;
			struct {
				unsigned char ENB:8;
			} BIT;
		} BCNT1AER;
	};
	char           wk12[1];
	union {
		union {
			unsigned short WORD;
			struct {
				unsigned short :8;
				unsigned short YR10:4;
				unsigned short YR1:4;
			} BIT;
		} RYRAR;
		union {
			unsigned short WORD;
			struct {
				unsigned short :8;
				unsigned short ENB:8;
			} BIT;
		} BCNT2AER;
	};
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char ENB:1;
			} BIT;
		} RYRAREN;
		union {
			unsigned char BYTE;
			struct {
				unsigned char ENB:8;
			} BIT;
		} BCNT3AER;
	};
	char           wk13[3];
	union {
		unsigned char BYTE;
		struct {
			unsigned char PES:4;
			unsigned char RTCOS:1;
			unsigned char PIE:1;
			unsigned char CIE:1;
			unsigned char AIE:1;
		} BIT;
	} RCR1;
	char           wk14[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char CNTMD:1;
			unsigned char HR24:1;
			unsigned char AADJP:1;
			unsigned char AADJE:1;
			unsigned char RTCOE:1;
			unsigned char ADJ30:1;
			unsigned char RESET:1;
			unsigned char START:1;
		} BIT;
	} RCR2;
	char           wk15[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char RTCDV:3;
			unsigned char RTCEN:1;
		} BIT;
	} RCR3;
	char           wk16[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char RCKSEL:1;
		} BIT;
	} RCR4;
	char           wk17[1];
	union {
		unsigned short WORD;
		struct {
			unsigned short :15;
			unsigned short RFC:1;
		} BIT;
	} RFRH;
	union {
		unsigned short WORD;
		struct {
			unsigned short RFC:16;
		} BIT;
	} RFRL;
	union {
		unsigned char BYTE;
		struct {
			unsigned char PMADJ:2;
			unsigned char ADJ:6;
		} BIT;
	} RADJ;
	char           wk18[17];
	union {
		unsigned char BYTE;
		struct {
			unsigned char TCEN:1;
			unsigned char :1;
			unsigned char TCNF:2;
			unsigned char :1;
			unsigned char TCST:1;
			unsigned char TCCT:2;
		} BIT;
	} RTCCR0;
	char           wk19[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char TCEN:1;
			unsigned char :1;
			unsigned char TCNF:2;
			unsigned char :1;
			unsigned char TCST:1;
			unsigned char TCCT:2;
		} BIT;
	} RTCCR1;
	char           wk20[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char TCEN:1;
			unsigned char :1;
			unsigned char TCNF:2;
			unsigned char :1;
			unsigned char TCST:1;
			unsigned char TCCT:2;
		} BIT;
	} RTCCR2;
	char           wk21[13];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char :1;
				unsigned char SEC10:3;
				unsigned char SEC1:4;
			} BIT;
		} RSECCP0;
		union {
			unsigned char BYTE;
			struct {
				unsigned char BCNCP0:8;
			} BIT;
		} BCNT0CP0;
	};
	char           wk22[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char :1;
				unsigned char MIN10:3;
				unsigned char MIN1:4;
			} BIT;
		} RMINCP0;
		union {
			unsigned char BYTE;
			struct {
				unsigned char BCNCP0:8;
			} BIT;
		} BCNT1CP0;
	};
	char           wk23[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char :1;
				unsigned char PM:1;
				unsigned char HR10:2;
				unsigned char HR1:4;
			} BIT;
		} RHRCP0;
		union {
			unsigned char BYTE;
			struct {
				unsigned char BCNCP0:8;
			} BIT;
		} BCNT2CP0;
	};
	char           wk24[3];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char :2;
				unsigned char DATE10:2;
				unsigned char DATE1:4;
			} BIT;
		} RDAYCP0;
		union {
			unsigned char BYTE;
			struct {
				unsigned char BCNCP0:8;
			} BIT;
		} BCNT3CP0;
	};
	char           wk25[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char MON10:1;
			unsigned char MON1:4;
		} BIT;
	} RMONCP0;
	char           wk26[5];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char :1;
				unsigned char SEC10:3;
				unsigned char SEC1:4;
			} BIT;
		} RSECCP1;
		union {
			unsigned char BYTE;
			struct {
				unsigned char BCNCP1:8;
			} BIT;
		} BCNT0CP1;
	};
	char           wk27[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char :1;
				unsigned char MIN10:3;
				unsigned char MIN1:4;
			} BIT;
		} RMINCP1;
		union {
			unsigned char BYTE;
			struct {
				unsigned char BCNCP1:8;
			} BIT;
		} BCNT1CP1;
	};
	char           wk28[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char :1;
				unsigned char PM:1;
				unsigned char HR10:2;
				unsigned char HR1:4;
			} BIT;
		} RHRCP1;
		union {
			unsigned char BYTE;
			struct {
				unsigned char BCNCP1:8;
			} BIT;
		} BCNT2CP1;
	};
	char           wk29[3];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char :2;
				unsigned char DATE10:2;
				unsigned char DATE1:4;
			} BIT;
		} RDAYCP1;
		union {
			unsigned char BYTE;
			struct {
				unsigned char BCNCP1:8;
			} BIT;
		} BCNT3CP1;
	};
	char           wk30[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char MON10:1;
			unsigned char MON1:4;
		} BIT;
	} RMONCP1;
	char           wk31[5];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char :1;
				unsigned char SEC10:3;
				unsigned char SEC1:4;
			} BIT;
		} RSECCP2;
		union {
			unsigned char BYTE;
			struct {
				unsigned char BCNCP2:8;
			} BIT;
		} BCNT0CP2;
	};
	char           wk32[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char :1;
				unsigned char MIN10:3;
				unsigned char MIN1:4;
			} BIT;
		} RMINCP2;
		union {
			unsigned char BYTE;
			struct {
				unsigned char BCNCP2:8;
			} BIT;
		} BCNT1CP2;
	};
	char           wk33[1];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char :1;
				unsigned char PM:1;
				unsigned char HR10:2;
				unsigned char HR1:4;
			} BIT;
		} RHRCP2;
		union {
			unsigned char BYTE;
			struct {
				unsigned char BCNCP2:8;
			} BIT;
		} BCNT2CP2;
	};
	char           wk34[3];
	union {
		union {
			unsigned char BYTE;
			struct {
				unsigned char :2;
				unsigned char DATE10:2;
				unsigned char DATE1:4;
			} BIT;
		} RDAYCP2;
		union {
			unsigned char BYTE;
			struct {
				unsigned char BCNCP2:8;
			} BIT;
		} BCNT3CP2;
	};
	char           wk35[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char MON10:1;
			unsigned char MON1:4;
		} BIT;
	} RMONCP2;
};

struct st_s12ad {
	union {
		unsigned short WORD;
		struct {
			unsigned short ADST:1;
			unsigned short ADCS:2;
			unsigned short ADIE:1;
			unsigned short :2;
			unsigned short TRGE:1;
			unsigned short EXTRG:1;
			unsigned short DBLE:1;
			unsigned short GBADIE:1;
			unsigned short :1;
			unsigned short DBLANS:5;
		} BIT;
	} ADCSR;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short ANSA0:16;
		} BIT;
	} ADANSA0;
	char           wk1[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short ADS0:16;
		} BIT;
	} ADADS0;
	char           wk2[2];
	union {
		unsigned char BYTE;
		struct {
			unsigned char AVEE:1;
			unsigned char :5;
			unsigned char ADC:2;
		} BIT;
	} ADADC;
	char           wk3[1];
	union {
		unsigned short WORD;
		struct {
			unsigned short ADRFMT:1;
			unsigned short :3;
			unsigned short DIAGM:1;
			unsigned short DIAGLD:1;
			unsigned short DIAGVAL:2;
			unsigned short :2;
			unsigned short ACE:1;
			unsigned short :2;
			unsigned short ADPRC:2;
		} BIT;
	} ADCER;
	union {
		unsigned short WORD;
		struct {
			unsigned short :2;
			unsigned short TRSA:6;
			unsigned short :2;
			unsigned short TRSB:6;
		} BIT;
	} ADSTRGR;
	char           wk4[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short ANSB0:16;
		} BIT;
	} ADANSB0;
	char           wk5[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short :2;
			unsigned short AD:12;
		} BIT;
	} ADDBLDR;
	char           wk6[4];
	union {
		unsigned short WORD;
		union {
			struct {
				unsigned short DIAGST:2;
				unsigned short :2;
				unsigned short AD:12;
			} RIGHT;
			struct {
				unsigned short AD:12;
				unsigned short :2;
				unsigned short DIAGST:2;
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
	char           wk7[48];
	unsigned char  ADSSTR0;
	char           wk8[5];
	union {
		unsigned short WORD;
		struct {
			unsigned short :5;
			unsigned short SHANS:3;
			unsigned short SSTSH:8;
		} BIT;
	} ADSHCR;
	char           wk9[11];
	unsigned char  ADSSTR1;
	unsigned char  ADSSTR2;
	unsigned char  ADSSTR3;
	unsigned char  ADSSTR4;
	unsigned char  ADSSTR5;
	unsigned char  ADSSTR6;
	unsigned char  ADSSTR7;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char ADNDIS:5;
		} BIT;
	} ADDISCR;
	char           wk9a[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char SHMD:1;
		} BIT;
	} ADSHMSR;
	char           wk10[3];
	union {
		unsigned short WORD;
		struct {
			unsigned short GBRP:1;
			unsigned short :13;
			unsigned short GBRSCN:1;
			unsigned short PGS:1;
		} BIT;
	} ADGSPCR;
	char           wk11[2];
	unsigned short ADDBLDRA;
	unsigned short ADDBLDRB;
	char           wk12[8];
	union {
		unsigned char BYTE;
		struct {
			unsigned char CMPIE:1;
			unsigned char WCMPE:1;
		} BIT;
	} ADCMPCR;
	char           wk13[3];
	union {
		unsigned short WORD;
		struct {
			unsigned short CMPS0:16;
		} BIT;
	} ADCMPANSR0;
	char           wk14[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short CMPL0:16;
		} BIT;
	} ADCMPLR0;
	char           wk15[2];
	unsigned short ADCMPDR0;
	unsigned short ADCMPDR1;
	union {
		unsigned short WORD;
		struct {
			unsigned short CMPF0:16;
		} BIT;
	} ADCMPSR0;
};

struct st_s12ad1 {
	union {
		unsigned short WORD;
		struct {
			unsigned short ADST:1;
			unsigned short ADCS:2;
			unsigned short ADIE:1;
			unsigned short :2;
			unsigned short TRGE:1;
			unsigned short EXTRG:1;
			unsigned short DBLE:1;
			unsigned short GBADIE:1;
			unsigned short :1;
			unsigned short DBLANS:5;
		} BIT;
	} ADCSR;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short ANSA0:16;
		} BIT;
	} ADANSA0;
	union {
		unsigned short WORD;
		struct {
			unsigned short :11;
			unsigned short ANSA1:5;
		} BIT;
	} ADANSA1;
	union {
		unsigned short WORD;
		struct {
			unsigned short ADS0:16;
		} BIT;
	} ADADS0;
	union {
		unsigned short WORD;
		struct {
			unsigned short :11;
			unsigned short ADS1:5;
		} BIT;
	} ADADS1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char AVEE:1;
			unsigned char :5;
			unsigned char ADC:2;
		} BIT;
	} ADADC;
	char           wk1[1];
	union {
		unsigned short WORD;
		struct {
			unsigned short ADRFMT:1;
			unsigned short :3;
			unsigned short DIAGM:1;
			unsigned short DIAGLD:1;
			unsigned short DIAGVAL:2;
			unsigned short :2;
			unsigned short ACE:1;
			unsigned short :2;
			unsigned short ADPRC:2;
		} BIT;
	} ADCER;
	union {
		unsigned short WORD;
		struct {
			unsigned short :2;
			unsigned short TRSA:6;
			unsigned short :2;
			unsigned short TRSB:6;
		} BIT;
	} ADSTRGR;
	union {
		unsigned short WORD;
		struct {
			unsigned short EXOEN:1;
			unsigned short EXSEL:2;
			unsigned short :1;
			unsigned short OCSB:1;
			unsigned short TSSB:1;
			unsigned short OCSA:1;
			unsigned short TSSA:1;
			unsigned short :6;
			unsigned short OCSAD:1;
			unsigned short TSSAD:1;
		} BIT;
	} ADEXICR;
	union {
		unsigned short WORD;
		struct {
			unsigned short ANSB0:16;
		} BIT;
	} ADANSB0;
	union {
		unsigned short WORD;
		struct {
			unsigned short :11;
			unsigned short ANSB1:5;
		} BIT;
	} ADANSB1;
	unsigned short ADDBLDR;
	unsigned short ADTSDR;
	unsigned short ADOCDR;
	union {
		unsigned short WORD;
		union {
			struct {
				unsigned short DIAGST:2;
				unsigned short :2;
				unsigned short AD:12;
			} RIGHT;
			struct {
				unsigned short AD:12;
				unsigned short :2;
				unsigned short DIAGST:2;
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
	char           wk2[22];
	unsigned char  ADSSTR0;
	unsigned char  ADSSTRL;
	char           wk3[14];
	unsigned char  ADSSTRT;
	unsigned char  ADSSTRO;
	char           wk4[1];
	unsigned char  ADSSTR1;
	unsigned char  ADSSTR2;
	unsigned char  ADSSTR3;
	unsigned char  ADSSTR4;
	unsigned char  ADSSTR5;
	unsigned char  ADSSTR6;
	unsigned char  ADSSTR7;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char ADNDIS:5;
		} BIT;
	} ADDISCR;
	char           wk5[5];
	union {
		unsigned short WORD;
		struct {
			unsigned short GBRP:1;
			unsigned short :13;
			unsigned short GBRSCN:1;
			unsigned short PGS:1;
		} BIT;
	} ADGSPCR;
	char           wk6[2];
	unsigned short ADDBLDRA;
	unsigned short ADDBLDRB;
	char           wk7[8];
	union {
		unsigned char BYTE;
		struct {
			unsigned char CMPIE:1;
			unsigned char WCMPE:1;
		} BIT;
	} ADCMPCR;
	char           wk8[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char CMPSOC:1;
			unsigned char CMPSTS:1;
		} BIT;
	} ADCMPANSER;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char CMPLOC:1;
			unsigned char CMPLTS:1;
		} BIT;
	} ADCMPLER;
	union {
		unsigned short WORD;
		struct {
			unsigned short CMPS0:16;
		} BIT;
	} ADCMPANSR0;
	union {
		unsigned short WORD;
		struct {
			unsigned short :11;
			unsigned short CMPS1:5;
		} BIT;
	} ADCMPANSR1;
	union {
		unsigned short WORD;
		struct {
			unsigned short CMPL0:16;
		} BIT;
	} ADCMPLR0;
	union {
		unsigned short WORD;
		struct {
			unsigned short :11;
			unsigned short CMPL1:5;
		} BIT;
	} ADCMPLR1;
	unsigned short ADCMPDR0;
	unsigned short ADCMPDR1;
	union {
		unsigned short WORD;
		struct {
			unsigned short CMPF0:16;
		} BIT;
	} ADCMPSR0;
	union {
		unsigned short WORD;
		struct {
			unsigned short :11;
			unsigned short CMPF1:5;
		} BIT;
	} ADCMPSR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char CMPFOC:1;
			unsigned char CMPFTS:1;
		} BIT;
	} ADCMPSER;
};

struct st_sci0 {
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
			unsigned char BCP2:1;
			unsigned char :2;
			unsigned char CHR1:1;
			unsigned char SDIR:1;
			unsigned char SINV:1;
			unsigned char :1;
			unsigned char SMIF:1;
		} BIT;
	} SCMR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char RXDESEL:1;
			unsigned char BGDM:1;
			unsigned char NFEN:1;
			unsigned char ABCS:1;
			unsigned char :1;
			unsigned char BRME:1;
			unsigned char :1;
			unsigned char ACS0:1;
		} BIT;
	} SEMR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char NFCS:3;
		} BIT;
	} SNFR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char IICDL:5;
			unsigned char :2;
			unsigned char IICM:1;
		} BIT;
	} SIMR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char IICACKT:1;
			unsigned char :3;
			unsigned char IICCSC:1;
			unsigned char IICINTM:1;
		} BIT;
	} SIMR2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char IICSCLS:2;
			unsigned char IICSDAS:2;
			unsigned char IICSTIF:1;
			unsigned char IICSTPREQ:1;
			unsigned char IICRSTAREQ:1;
			unsigned char IICSTAREQ:1;
		} BIT;
	} SIMR3;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char IICACKR:1;
		} BIT;
	} SISR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char CKPH:1;
			unsigned char CKPOL:1;
			unsigned char :1;
			unsigned char MFF:1;
			unsigned char :1;
			unsigned char MSS:1;
			unsigned char CTSE:1;
			unsigned char SSE:1;
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
};

struct st_sci12 {
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
			unsigned char BCP2:1;
			unsigned char :2;
			unsigned char CHR1:1;
			unsigned char SDIR:1;
			unsigned char SINV:1;
			unsigned char :1;
			unsigned char SMIF:1;
		} BIT;
	} SCMR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char RXDESEL:1;
			unsigned char BGDM:1;
			unsigned char NFEN:1;
			unsigned char ABCS:1;
			unsigned char :1;
			unsigned char BRME:1;
			unsigned char :1;
			unsigned char ACS0:1;
		} BIT;
	} SEMR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char NFCS:3;
		} BIT;
	} SNFR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char IICDL:5;
			unsigned char :2;
			unsigned char IICM:1;
		} BIT;
	} SIMR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char IICACKT:1;
			unsigned char :3;
			unsigned char IICCSC:1;
			unsigned char IICINTM:1;
		} BIT;
	} SIMR2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char IICSCLS:2;
			unsigned char IICSDAS:2;
			unsigned char IICSTIF:1;
			unsigned char IICSTPREQ:1;
			unsigned char IICRSTAREQ:1;
			unsigned char IICSTAREQ:1;
		} BIT;
	} SIMR3;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char IICACKR:1;
		} BIT;
	} SISR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char CKPH:1;
			unsigned char CKPOL:1;
			unsigned char :1;
			unsigned char MFF:1;
			unsigned char :1;
			unsigned char MSS:1;
			unsigned char CTSE:1;
			unsigned char SSE:1;
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
			unsigned char :7;
			unsigned char ESME:1;
		} BIT;
	} ESMER;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char BRME:1;
			unsigned char RXDSF:1;
			unsigned char SFSF:1;
		} BIT;
	} CR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char PIBS:3;
			unsigned char PIBE:1;
			unsigned char CF1DS:2;
			unsigned char CF0RE:1;
			unsigned char BFE:1;
		} BIT;
	} CR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char RTS:2;
			unsigned char BCCS:2;
			unsigned char :1;
			unsigned char DFCS:3;
		} BIT;
	} CR2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char SDST:1;
		} BIT;
	} CR3;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char SHARPS:1;
			unsigned char :2;
			unsigned char RXDXPS:1;
			unsigned char TXDXPS:1;
		} BIT;
	} PCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char AEDIE:1;
			unsigned char BCDIE:1;
			unsigned char PIBDIE:1;
			unsigned char CF1MIE:1;
			unsigned char CF0MIE:1;
			unsigned char BFDIE:1;
		} BIT;
	} ICR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char AEDF:1;
			unsigned char BCDF:1;
			unsigned char PIBDF:1;
			unsigned char CF1MF:1;
			unsigned char CF0MF:1;
			unsigned char BFDF:1;
		} BIT;
	} STR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char AEDCL:1;
			unsigned char BCDCL:1;
			unsigned char PIBDCL:1;
			unsigned char CF1MCL:1;
			unsigned char CF0MCL:1;
			unsigned char BFDCL:1;
		} BIT;
	} STCR;
	unsigned char  CF0DR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char CF0CE7:1;
			unsigned char CF0CE6:1;
			unsigned char CF0CE5:1;
			unsigned char CF0CE4:1;
			unsigned char CF0CE3:1;
			unsigned char CF0CE2:1;
			unsigned char CF0CE1:1;
			unsigned char CF0CE0:1;
		} BIT;
	} CF0CR;
	unsigned char  CF0RR;
	unsigned char  PCF1DR;
	unsigned char  SCF1DR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char CF1CE7:1;
			unsigned char CF1CE6:1;
			unsigned char CF1CE5:1;
			unsigned char CF1CE4:1;
			unsigned char CF1CE3:1;
			unsigned char CF1CE2:1;
			unsigned char CF1CE1:1;
			unsigned char CF1CE0:1;
		} BIT;
	} CF1CR;
	unsigned char  CF1RR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char TCST:1;
		} BIT;
	} TCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char TCSS:3;
			unsigned char TWRC:1;
			unsigned char :1;
			unsigned char TOMS:2;
		} BIT;
	} TMR;
	unsigned char  TPRE;
	unsigned char  TCNT;
};

struct st_scifa {
	union {
		unsigned short WORD;
		struct {
			unsigned short :8;
			unsigned short CM:1;
			unsigned short CHR:1;
			unsigned short PE:1;
			unsigned short PM:1;
			unsigned short STOP:1;
			unsigned short :1;
			unsigned short CKS:2;
		} BIT;
	} SMR;
//	unsigned char  BRR;
	union {
		unsigned char  BRR;
		unsigned char  MDDR;
	};
	char           wk0[1];
	union {
		unsigned short WORD;
		struct {
			unsigned short :8;
			unsigned short TIE:1;
			unsigned short RIE:1;
			unsigned short TE:1;
			unsigned short RE:1;
			unsigned short REIE:1;
			unsigned short TEIE:1;
			unsigned short CKE:2;
		} BIT;
	} SCR;
	unsigned char  FTDR;
	char           wk1[1];
	union {
		unsigned short WORD;
		struct {
			unsigned short :8;
			unsigned short ER:1;
			unsigned short TEND:1;
			unsigned short TDFE:1;
			unsigned short BRK:1;
			unsigned short FER:1;
			unsigned short PER:1;
			unsigned short RDF:1;
			unsigned short DR:1;
		} BIT;
	} FSR;
	unsigned char  FRDR;
	char           wk2[1];
	union {
		unsigned short WORD;
		struct {
			unsigned short :5;
			unsigned short RSTRG:3;
			unsigned short RTRG:2;
			unsigned short TTRG:2;
			unsigned short MCE:1;
			unsigned short TFRST:1;
			unsigned short RFRST:1;
			unsigned short LOOP:1;
		} BIT;
	} FCR;
	union {
		unsigned short WORD;
		struct {
			unsigned short :3;
			unsigned short T:5;
			unsigned short :3;
			unsigned short R:5;
		} BIT;
	} FDR;
	union {
		unsigned short WORD;
		struct {
			unsigned short :8;
			unsigned short RTS2IO:1;
			unsigned short RTS2DT:1;
			unsigned short CTS2IO:1;
			unsigned short CTS2DT:1;
			unsigned short SCKIO:1;
			unsigned short SCKDT:1;
			unsigned short SPB2IO:1;
			unsigned short SPB2DT:1;
		} BIT;
	} SPTR;
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short PER:4;
			unsigned short :2;
			unsigned short FER:4;
			unsigned short :1;
			unsigned short ORER:1;
		} BIT;
	} LSR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char BGDM:1;
			unsigned char :1;
			unsigned char BRME:1;
			unsigned char MDDRS:1;
			unsigned char DIR:1;
			unsigned char NFEN:1;
			unsigned char :1;
			unsigned char ABCS0:1;
		} BIT;
	} SEMR;
	char           wk3[1];
	union {
		unsigned short WORD;
		struct {
			unsigned short RTRGS:1;
			unsigned short :2;
			unsigned short RFTC:5;
			unsigned short TTRGS:1;
			unsigned short :2;
			unsigned short TFTC:5;
		} BIT;
	} FTCR;
};

struct st_sdhi {
	union {
		unsigned long LONG;
//		struct {
//			unsigned long :16;
//			unsigned long CMD12AT:2;
//			unsigned long TRSTP:1;
//			unsigned long CMDRW:1;
//			unsigned long CMDTP:1;
//			unsigned long RSPTP:3;
//			unsigned long ACMD:2;
//			unsigned long CMDIDX:6;
//		} BIT;
	} SDCMD;
	char           wk0[4];
	unsigned long  SDARG;
	char           wk1[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :23;
			unsigned long SDBLKCNTEN:1;
			unsigned long :7;
			unsigned long STP:1;
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
//		struct {
//			unsigned long :21;
//			unsigned long SDD3MON:1;
//			unsigned long SDD3IN:1;
//			unsigned long SDD3RM:1;
//			unsigned long SDWPMON:1;
//			unsigned long :1;
//			unsigned long SDCDMON:1;
//			unsigned long SDCDIN:1;
//			unsigned long SDCDRM:1;
//			unsigned long ACEND:1;
//			unsigned long :1;
//			unsigned long RSPEND:1;
//		} BIT;
	} SDSTS1;
	union {
		unsigned long LONG;
//		struct {
//			unsigned long :16;
//			unsigned long ILA:1;
//			unsigned long CBSY:1;
//			unsigned long SDCLKCREN:1;
//			unsigned long :3;
//			unsigned long BWE:1;
//			unsigned long BRE:1;
//			unsigned long SDD0MON:1;
//			unsigned long RSPTO:1;
//			unsigned long ILR:1;
//			unsigned long ILW:1;
//			unsigned long DTO:1;
//			unsigned long ENDE:1;
//			unsigned long CRCE:1;
//			unsigned long CMDE:1;
//		} BIT;
	} SDSTS2;
	union {
		unsigned long LONG;
		struct {
			unsigned long :22;
			unsigned long SDD3INM:1;
			unsigned long SDD3RMM:1;
			unsigned long :3;
			unsigned long SDCDINM:1;
			unsigned long SDCDRMM:1;
			unsigned long ACENDM:1;
			unsigned long :1;
			unsigned long RSPENDM:1;
		} BIT;
	} SDIMSK1;
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long ILAM:1;
			unsigned long :5;
			unsigned long BWEM:1;
			unsigned long BREM:1;
			unsigned long :1;
			unsigned long RSPTOM:1;
			unsigned long ILRM:1;
			unsigned long ILWM:1;
			unsigned long DTTOM:1;
			unsigned long ENDEM:1;
			unsigned long CRCEM:1;
			unsigned long CMDEM:1;
		} BIT;
	} SDIMSK2;
	union {
		unsigned long LONG;
		struct {
			unsigned long :22;
			unsigned long CLKCTRLEN:1;
			unsigned long CLKEN:1;
			unsigned long CLKSEL:8;
		} BIT;
	} SDCLKCR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :22;
			unsigned long LEN:10;
		} BIT;
	} SDSIZE;
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long WIDTH:1;
			unsigned long :7;
			unsigned long TOP:4;
			unsigned long CTOP:4;
		} BIT;
	} SDOPT;
	char           wk6[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :17;
			unsigned long CRCTK:3;
			unsigned long CRCTKE:1;
			unsigned long RDCRCE:1;
			unsigned long RSPCRCE1:1;
			unsigned long RSPCRCE0:1;
			unsigned long :2;
			unsigned long CRCLENE:1;
			unsigned long RDLENE:1;
			unsigned long RSPLENE1:1;
			unsigned long RSPLENE0:1;
			unsigned long CMDE1:1;
			unsigned long CMDE0:1;
		} BIT;
	} SDERSTS1;
	union {
		unsigned long LONG;
		struct {
			unsigned long :25;
			unsigned long CRCBSYTO:1;
			unsigned long CRCTO:1;
			unsigned long RDTO:1;
			unsigned long BSYTO1:1;
			unsigned long BSYTO0:1;
			unsigned long RSPTO1:1;
			unsigned long RSPTO0:1;
		} BIT;
	} SDERSTS2;
	unsigned long  SDBUFR;
	char           wk7[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :22;
			unsigned long C52PUB:1;
			unsigned long IOABT:1;
			unsigned long :5;
			unsigned long RWREQ:1;
			unsigned long :1;
			unsigned long INTEN:1;
		} BIT;
	} SDIOMD;
	union {
		unsigned long LONG;
//		struct {
//			unsigned long :16;
//			unsigned long EXWT:1;
//			unsigned long EXPUB52:1;
//			unsigned long :13;
//			unsigned long IOIRQ:1;
//		} BIT;
	} SDIOSTS;
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long EXWTM:1;
			unsigned long EXPUB52M:1;
			unsigned long :13;
			unsigned long IOIRQM:1;
		} BIT;
	} SDIOIMSK;
	char           wk8[316];
	union {
		unsigned long LONG;
		struct {
			unsigned long :30;
			unsigned long DMAEN:1;
		} BIT;
	} SDDMAEN;
	char           wk9[12];
	union {
		unsigned long LONG;
		struct {
			unsigned long :31;
			unsigned long SDRST:1;
		} BIT;
	} SDRST;
	union {
		unsigned long LONG;
		struct {
			unsigned long :16;
			unsigned long CPRM:1;
			unsigned long CLKRAT:1;
			unsigned long :2;
			unsigned long IP2:4;
			unsigned long IP1:8;
		} BIT;
	} SDVER;
	char           wk10[24];
	union {
		unsigned long LONG;
		struct {
			unsigned long :24;
			unsigned long BRSWP:1;
			unsigned long BWSWP:1;
		} BIT;
	} SDSWAP;
};

struct st_smci0 {
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
			unsigned char ERS:1;
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
			unsigned char BCP2:1;
			unsigned char :2;
			unsigned char CHR1:1;
			unsigned char SDIR:1;
			unsigned char SINV:1;
			unsigned char :1;
			unsigned char SMIF:1;
		} BIT;
	} SCMR;
};

struct st_src {
	union {
		unsigned long LONG;
	} SRCFCTR[5552];
	char           wk0[2352];
	union {
		unsigned long LONG;
	} SRCID;
	union {
		unsigned long LONG;
	} SRCOD;
	union {
		unsigned short WORD;
		struct {
			unsigned short :6;
			unsigned short IED:1;
			unsigned short IEN:1;
			unsigned short :6;
			unsigned short IFTRG:2;
		} BIT;
	} SRCIDCTRL;
	union {
		unsigned short WORD;
		struct {
			unsigned short :5;
			unsigned short OCH:1;
			unsigned short OED:1;
			unsigned short OEN:1;
			unsigned short :6;
			unsigned short OFTRG:2;
		} BIT;
	} SRCODCTRL;
	union {
		unsigned short WORD;
		struct {
			unsigned short FICRAE:1;
			unsigned short :1;
			unsigned short CEEN:1;
			unsigned short SRCEN:1;
			unsigned short UDEN:1;
			unsigned short OVEN:1;
			unsigned short FL:1;
			unsigned short CL:1;
			unsigned short IFS:4;
			unsigned short :1;
			unsigned short OFS:3;
		} BIT;
	} SRCCTRL;
	union {
		unsigned short WORD;
		struct {
			unsigned short OFDN:5;
			unsigned short IFDN:4;
			unsigned short :1;
			unsigned short CEF:1;
			unsigned short FLF:1;
			unsigned short UDF:1;
			unsigned short OVF:1;
			unsigned short IINT:1;
			unsigned short OINT:1;
		} BIT;
	} SRCSTAT;
};

struct st_ssi {
	union {
		unsigned long LONG;
		struct {
			unsigned long :1;
			unsigned long CKS:1;
			unsigned long TUIEN:1;
			unsigned long TOIEN:1;
			unsigned long RUIEN:1;
			unsigned long ROIEN:1;
			unsigned long IIEN:1;
			unsigned long :1;
			unsigned long CHNL:2;
			unsigned long DWL:3;
			unsigned long SWL:3;
			unsigned long SCKD:1;
			unsigned long SWSD:1;
			unsigned long SCKP:1;
			unsigned long SWSP:1;
			unsigned long SPDP:1;
			unsigned long SDTA:1;
			unsigned long PDTA:1;
			unsigned long DEL:1;
			unsigned long CKDV:4;
			unsigned long MUEN:1;
			unsigned long :1;
			unsigned long TEN:1;
			unsigned long REN:1;
		} BIT;
	} SSICR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :2;
			unsigned long TUIRQ:1;
			unsigned long TOIRQ:1;
			unsigned long RUIRQ:1;
			unsigned long ROIRQ:1;
			unsigned long IIRQ:1;
			unsigned long :18;
			unsigned long TCHNO:2;
			unsigned long TSWNO:1;
			unsigned long RCHNO:2;
			unsigned long RSWNO:1;
			unsigned long IDST:1;
		} BIT;
	} SSISR;
	char           wk0[8];
	union {
		unsigned long LONG;
		struct {
			unsigned long AUCKE:1;
			unsigned long :14;
			unsigned long SSIRST:1;
			unsigned long :8;
			unsigned long TTRG:2;
			unsigned long RTRG:2;
			unsigned long TIE:1;
			unsigned long RIE:1;
			unsigned long TFRST:1;
			unsigned long RFRST:1;
		} BIT;
	} SSIFCR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :4;
			unsigned long TDC:4;
			unsigned long :7;
			unsigned long TDE:1;
			unsigned long :4;
			unsigned long RDC:4;
			unsigned long :7;
			unsigned long RDF:1;
		} BIT;
	} SSIFSR;
	unsigned long  SSIFTDR;
	unsigned long  SSIFRDR;
	union {
		unsigned long LONG;
		struct {
			unsigned long :23;
			unsigned long CONT:1;
		} BIT;
	} SSITDMR;
};

struct st_system {
	union {
		unsigned short WORD;
		struct {
			unsigned short :15;
			unsigned short MD:1;
		} BIT;
	} MDMONR;
	union {
		unsigned short WORD;
		struct {
			unsigned short :10;
			unsigned short UBTS:1;
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
			unsigned short :8;
			unsigned short SBYRAME:1;
			unsigned short ECCRAME:1;
			unsigned short :5;
			unsigned short RAME:1;
		} BIT;
	} SYSCR1;
	char           wk1[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short SSBY:1;
			unsigned short OPE:1;
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
			unsigned long MSTPA27:1;
			unsigned long :2;
			unsigned long MSTPA24:1;
			unsigned long :4;
			unsigned long MSTPA19:1;
			unsigned long :1;
			unsigned long MSTPA17:1;
			unsigned long MSTPA16:1;
			unsigned long MSTPA15:1;
			unsigned long MSTPA14:1;
			unsigned long MSTPA13:1;
			unsigned long :1;
			unsigned long MSTPA11:1;
			unsigned long MSTPA10:1;
			unsigned long MSTPA9:1;
			unsigned long :1;
			unsigned long MSTPA7:1;
			unsigned long :1;
			unsigned long MSTPA5:1;
			unsigned long MSTPA4:1;
			unsigned long :2;
			unsigned long MSTPA1:1;
			unsigned long MSTPA0:1;
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
			unsigned long MSTPB24:1;
			unsigned long MSTPB23:1;
			unsigned long MSTPB22:1;
			unsigned long MSTPB21:1;
			unsigned long :1;
			unsigned long MSTPB19:1;
			unsigned long :1;
			unsigned long MSTPB17:1;
			unsigned long MSTPB16:1;
			unsigned long MSTPB15:1;
			unsigned long MSTPB14:1;
			unsigned long :1;
			unsigned long MSTPB12:1;
			unsigned long :2;
			unsigned long MSTPB9:1;
			unsigned long MSTPB8:1;
			unsigned long :1;
			unsigned long MSTPB6:1;
			unsigned long :1;
			unsigned long MSTPB4:1;
			unsigned long :1;
			unsigned long MSTPB2:1;
			unsigned long MSTPB1:1;
			unsigned long MSTPB0:1;
		} BIT;
	} MSTPCRB;
	union {
		unsigned long LONG;
		struct {
			unsigned long :4;
			unsigned long MSTPC27:1;
			unsigned long MSTPC26:1;
			unsigned long MSTPC25:1;
			unsigned long MSTPC24:1;
			unsigned long MSTPC23:1;
			unsigned long :3;
			unsigned long MSTPC19:1;
			unsigned long :1;
			unsigned long MSTPC17:1;
			unsigned long :9;
			unsigned long MSTPC7:1;
			unsigned long MSTPC6:1;
			unsigned long :5;
			unsigned long MSTPC0:1;
		} BIT;
	} MSTPCRC;
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long MSTPD23:1;
			unsigned long :1;
			unsigned long MSTPD21:1;
			unsigned long :1;
			unsigned long MSTPD19:1;
			unsigned long :3;
			unsigned long MSTPD15:1;
			unsigned long MSTPD14:1;
			unsigned long :6;
			unsigned long MSTPD7:1;
			unsigned long MSTPD6:1;
			unsigned long MSTPD5:1;
			unsigned long MSTPD4:1;
			unsigned long MSTPD3:1;
			unsigned long MSTPD2:1;
			unsigned long MSTPD1:1;
			unsigned long MSTPD0:1;
		} BIT;
	} MSTPCRD;
	union {
		unsigned long LONG;
		struct {
			unsigned long FCK:4;
			unsigned long ICK:4;
			unsigned long PSTOP1:1;
			unsigned long PSTOP0:1;
			unsigned long :2;
			unsigned long BCK:4;
			unsigned long PCKA:4;
			unsigned long PCKB:4;
			unsigned long PCKC:4;
			unsigned long PCKD:4;
		} BIT;
	} SCKCR;
	union {
		unsigned short WORD;
		struct {
			unsigned short :8;
			unsigned short UCK:4;
		} BIT;
	} SCKCR2;
	union {
		unsigned short WORD;
		struct {
			unsigned short :5;
			unsigned short CKSEL:3;
		} BIT;
	} SCKCR3;
	union {
		unsigned short WORD;
		struct {
			unsigned short :2;
			unsigned short STC:6;
			unsigned short :3;
			unsigned short PLLSRCSEL:1;
			unsigned short :2;
			unsigned short PLIDIV:2;
		} BIT;
	} PLLCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char PLLEN:1;
		} BIT;
	} PLLCR2;
	char           wk3[5];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char BCLKDIV:1;
		} BIT;
	} BCKCR;
	char           wk4[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char MOSTP:1;
		} BIT;
	} MOSCCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char SOSTP:1;
		} BIT;
	} SOSCCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char LCSTP:1;
		} BIT;
	} LOCOCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char ILCSTP:1;
		} BIT;
	} ILOCOCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char HCSTP:1;
		} BIT;
	} HOCOCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char HCFRQ:2;
		} BIT;
	} HOCOCR2;
	char           wk5[4];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char ILCOVF:1;
			unsigned char HCOVF:1;
			unsigned char PLOVF:1;
			unsigned char SOOVF:1;
			unsigned char MOOVF:1;
		} BIT;
	} OSCOVFSR;
	char           wk6[3];
	union {
		unsigned char BYTE;
		struct {
			unsigned char OSTDE:1;
			unsigned char :6;
			unsigned char OSTDIE:1;
		} BIT;
	} OSTDCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char OSTDF:1;
		} BIT;
	} OSTDSR;
	char           wk7[94];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char OPCMTSF:1;
			unsigned char :1;
			unsigned char OPCM:3;
		} BIT;
	} OPCCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char RSTCKEN:1;
			unsigned char :4;
			unsigned char RSTCKSEL:3;
		} BIT;
	} RSTCKCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char MSTS:8;
		} BIT;
	} MOSCWTCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char SSTS:8;
		} BIT;
	} SOSCWTCR;
	char           wk8[28];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char SWRF:1;
			unsigned char WDTRF:1;
			unsigned char IWDTRF:1;
		} BIT;
	} RSTSR2;
	char           wk9[1];
	unsigned short SWRR;
	char           wk10[28];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char LVD1IRQSEL:1;
			unsigned char LVD1IDTSEL:2;
		} BIT;
	} LVD1CR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char LVD1MON:1;
			unsigned char LVD1DET:1;
		} BIT;
	} LVD1SR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char LVD2IRQSEL:1;
			unsigned char LVD2IDTSEL:2;
		} BIT;
	} LVD2CR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char LVD2MON:1;
			unsigned char LVD2DET:1;
		} BIT;
	} LVD2SR;
	char           wk11[794];
	union {
		unsigned short WORD;
		struct {
			unsigned short PRKEY:8;
			unsigned short :4;
			unsigned short PRC3:1;
			unsigned short :1;
			unsigned short PRC1:1;
			unsigned short PRC0:1;
		} BIT;
	} PRCR;
	char           wk12a[25104];
	union {
		unsigned long LONG;
		struct {
			unsigned long :31;
			unsigned long MEMWAIT:1;
		} BIT;
	} MEMWAIT;
	char           wk12b[23660];
	union {
		unsigned char BYTE;
		struct {
			unsigned char DPSBY:1;
			unsigned char IOKEEP:1;
			unsigned char :4;
			unsigned char DEEPCUT:2;
		} BIT;
	} DPSBYCR;
	char           wk13[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char DIRQ7E:1;
			unsigned char DIRQ6E:1;
			unsigned char DIRQ5E:1;
			unsigned char DIRQ4E:1;
			unsigned char DIRQ3E:1;
			unsigned char DIRQ2E:1;
			unsigned char DIRQ1E:1;
			unsigned char DIRQ0E:1;
		} BIT;
	} DPSIER0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char DIRQ15E:1;
			unsigned char DIRQ14E:1;
			unsigned char DIRQ13E:1;
			unsigned char DIRQ12E:1;
			unsigned char DIRQ11E:1;
			unsigned char DIRQ10E:1;
			unsigned char DIRQ9E:1;
			unsigned char DIRQ8E:1;
		} BIT;
	} DPSIER1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char DUSBIE:1;
			unsigned char DRIICCIE:1;
			unsigned char DRIICDIE:1;
			unsigned char DNMIE:1;
			unsigned char DRTCAIE:1;
			unsigned char DRTCIIE:1;
			unsigned char DLVD2IE:1;
			unsigned char DLVD1IE:1;
		} BIT;
	} DPSIER2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DCANIE:1;
		} BIT;
	} DPSIER3;
	union {
		unsigned char BYTE;
		struct {
			unsigned char DIRQ7F:1;
			unsigned char DIRQ6F:1;
			unsigned char DIRQ5F:1;
			unsigned char DIRQ4F:1;
			unsigned char DIRQ3F:1;
			unsigned char DIRQ2F:1;
			unsigned char DIRQ1F:1;
			unsigned char DIRQ0F:1;
		} BIT;
	} DPSIFR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char DIRQ15F:1;
			unsigned char DIRQ14F:1;
			unsigned char DIRQ13F:1;
			unsigned char DIRQ12F:1;
			unsigned char DIRQ11F:1;
			unsigned char DIRQ10F:1;
			unsigned char DIRQ9F:1;
			unsigned char DIRQ8F:1;
		} BIT;
	} DPSIFR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char DUSBIF:1;
			unsigned char DRIICCIF:1;
			unsigned char DRIICDIF:1;
			unsigned char DNMIF:1;
			unsigned char DRTCAIF:1;
			unsigned char DRTCIIF:1;
			unsigned char DLVD2IF:1;
			unsigned char DLVD1IF:1;
		} BIT;
	} DPSIFR2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DCANIF:1;
		} BIT;
	} DPSIFR3;
	union {
		unsigned char BYTE;
		struct {
			unsigned char DIRQ7EG:1;
			unsigned char DIRQ6EG:1;
			unsigned char DIRQ5EG:1;
			unsigned char DIRQ4EG:1;
			unsigned char DIRQ3EG:1;
			unsigned char DIRQ2EG:1;
			unsigned char DIRQ1EG:1;
			unsigned char DIRQ0EG:1;
		} BIT;
	} DPSIEGR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char DIRQ15EG:1;
			unsigned char DIRQ14EG:1;
			unsigned char DIRQ13EG:1;
			unsigned char DIRQ12EG:1;
			unsigned char DIRQ11EG:1;
			unsigned char DIRQ10EG:1;
			unsigned char DIRQ9EG:1;
			unsigned char DIRQ8EG:1;
		} BIT;
	} DPSIEGR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char DRIICCEG:1;
			unsigned char DRIICDEG:1;
			unsigned char DNMIEG:1;
			unsigned char :2;
			unsigned char DLVD2EG:1;
			unsigned char DLVD1EG:1;
		} BIT;
	} DPSIEGR2;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DCANIEG:1;
		} BIT;
	} DPSIEGR3;
	char           wk14[2];
	union {
		unsigned char BYTE;
		struct {
			unsigned char DPSRSTF:1;
			unsigned char :3;
			unsigned char LVD2RF:1;
			unsigned char LVD1RF:1;
			unsigned char LVD0RF:1;
			unsigned char PORF:1;
		} BIT;
	} RSTSR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char CWSF:1;
		} BIT;
	} RSTSR1;
	char           wk15[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char MOSEL:1;
			unsigned char MODRV2:2;
			unsigned char :3;
			unsigned char MOFXIN:1;
		} BIT;
	} MOFCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char HOCOPCNT:1;
		} BIT;
	} HOCOPCR;
	char           wk16[2];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char LVD2E:1;
			unsigned char LVD1E:1;
		} BIT;
	} LVCMPCR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char LVD2LVL:4;
			unsigned char LVD1LVL:4;
		} BIT;
	} LVDLVLR;
	char           wk17[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char LVD1RN:1;
			unsigned char LVD1RI:1;
			unsigned char LVD1FSAMP:2;
			unsigned char :1;
			unsigned char LVD1CMPE:1;
			unsigned char LVD1DFDIS:1;
			unsigned char LVD1RIE:1;
		} BIT;
	} LVD1CR0;
	union {
		unsigned char BYTE;
		struct {
			unsigned char LVD2RN:1;
			unsigned char LVD2RI:1;
			unsigned char LVD2FSAMP:2;
			unsigned char :1;
			unsigned char LVD2CMPE:1;
			unsigned char LVD2DFDIS:1;
			unsigned char LVD2RIE:1;
		} BIT;
	} LVD2CR0;
	char           wk18[4];
	unsigned char  DPSBKR[32];
};

struct st_temps {
	union {
		unsigned char BYTE;
		struct {
			unsigned char TSEN:1;
			unsigned char :2;
			unsigned char TSOE:1;
		} BIT;
	} TSCR;
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
	char           wk5[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char TCS:1;
		} BIT;
	} TCSTR;
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
	char           wk5[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char TCS:1;
		} BIT;
	} TCSTR;
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
			unsigned char :2;
			unsigned char NFCS:2;
			unsigned char NFDEN:1;
			unsigned char NFCEN:1;
			unsigned char NFBEN:1;
			unsigned char NFAEN:1;
		} BIT;
	} NFCR;
	char           wk0[7];
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
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char TCFV:1;
			unsigned char TGFD:1;
			unsigned char TGFC:1;
			unsigned char TGFB:1;
			unsigned char TGFA:1;
		} BIT;
	} TSR;
	unsigned short TCNT;
	unsigned short TGRA;
	unsigned short TGRB;
	unsigned short TGRC;
	unsigned short TGRD;
};

struct st_tpu1 {
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char NFCS:2;
			unsigned char :2;
			unsigned char NFBEN:1;
			unsigned char NFAEN:1;
		} BIT;
	} NFCR;
	char           wk1[22];
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
	char           wk2[1];
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
			unsigned char :1;
			unsigned char TCFU:1;
			unsigned char TCFV:1;
			unsigned char :2;
			unsigned char TGFB:1;
			unsigned char TGFA:1;
		} BIT;
	} TSR;
	unsigned short TCNT;
	unsigned short TGRA;
	unsigned short TGRB;
};

struct st_tpu2 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char NFCS:2;
			unsigned char :2;
			unsigned char NFBEN:1;
			unsigned char NFAEN:1;
		} BIT;
	} NFCR;
	char           wk0[37];
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
	char           wk1[1];
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
			unsigned char :1;
			unsigned char TCFU:1;
			unsigned char TCFV:1;
			unsigned char :2;
			unsigned char TGFB:1;
			unsigned char TGFA:1;
		} BIT;
	} TSR;
	unsigned short TCNT;
	unsigned short TGRA;
	unsigned short TGRB;
};

struct st_tpu3 {
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char NFCS:2;
			unsigned char NFDEN:1;
			unsigned char NFCEN:1;
			unsigned char NFBEN:1;
			unsigned char NFAEN:1;
		} BIT;
	} NFCR;
	char           wk1[52];
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
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char TCFV:1;
			unsigned char TGFD:1;
			unsigned char TGFC:1;
			unsigned char TGFB:1;
			unsigned char TGFA:1;
		} BIT;
	} TSR;
	unsigned short TCNT;
	unsigned short TGRA;
	unsigned short TGRB;
	unsigned short TGRC;
	unsigned short TGRD;
};

struct st_tpu4 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char NFCS:2;
			unsigned char :2;
			unsigned char NFBEN:1;
			unsigned char NFAEN:1;
		} BIT;
	} NFCR;
	char           wk0[67];
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
	char           wk1[1];
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
			unsigned char :1;
			unsigned char TCFU:1;
			unsigned char TCFV:1;
			unsigned char :2;
			unsigned char TGFB:1;
			unsigned char TGFA:1;
		} BIT;
	} TSR;
	unsigned short TCNT;
	unsigned short TGRA;
	unsigned short TGRB;
};

struct st_tpu5 {
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char NFCS:2;
			unsigned char :2;
			unsigned char NFBEN:1;
			unsigned char NFAEN:1;
		} BIT;
	} NFCR;
	char           wk1[82];
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
	char           wk2[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
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
			unsigned char :1;
			unsigned char TCFU:1;
			unsigned char TCFV:1;
			unsigned char :2;
			unsigned char TGFB:1;
			unsigned char TGFA:1;
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

struct st_usb {
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long DVBSTS0:1;
			unsigned long :1;
			unsigned long DOVCB0:1;
			unsigned long DOVCA0:1;
			unsigned long :2;
			unsigned long DM0:1;
			unsigned long DP0:1;
			unsigned long :11;
			unsigned long FIXPHY0:1;
			unsigned long DRPD0:1;
			unsigned long :1;
			unsigned long RPUE0:1;
			unsigned long SRPC0:1;
		} BIT;
	} DPUSR0R;
	union {
		unsigned long LONG;
		struct {
			unsigned long :8;
			unsigned long DVBINT0:1;
			unsigned long :1;
			unsigned long DOVRCRB0:1;
			unsigned long DOVRCRA0:1;
			unsigned long :2;
			unsigned long DMINT0:1;
			unsigned long DPINT0:1;
			unsigned long :8;
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
//		struct {
//			unsigned short :5;
//			unsigned short SCKE:1;
//			unsigned short :3;
//			unsigned short DCFM:1;
//			unsigned short DRPD:1;
//			unsigned short DPRPU:1;
//			unsigned short :3;
//			unsigned short USBE:1;
//		} BIT;
	} SYSCFG;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short OVCMON:2;
			unsigned short :7;
			unsigned short HTACT:1;
			unsigned short SOFEA:1;
			unsigned short :2;
			unsigned short IDMON:1;
			unsigned short LNST:2;
		} BIT;
	} SYSSTS0;
	char           wk1[2];
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :4;
//			unsigned short HNPBTOA:1;
//			unsigned short EXICEN:1;
//			unsigned short VBUSEN:1;
//			unsigned short WKUP:1;
//			unsigned short RWUPE:1;
//			unsigned short USBRST:1;
//			unsigned short RESUME:1;
//			unsigned short UACT:1;
//			unsigned short :1;
//			unsigned short RHST:3;
//		} BIT;
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
//		struct {
//			unsigned short RCNT:1;
//			unsigned short REW:1;
//			unsigned short :3;
//			unsigned short MBW:1;
//			unsigned short :1;
//			unsigned short BIGEND:1;
//			unsigned short :2;
//			unsigned short ISEL:1;
//			unsigned short :1;
//			unsigned short CURPIPE:4;
//		} BIT;
	} CFIFOSEL;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BVAL:1;
//			unsigned short BCLR:1;
//			unsigned short FRDY:1;
//			unsigned short :4;
//			unsigned short DTLN:9;
//		} BIT;
	} CFIFOCTR;
	char           wk6[4];
	union {
		unsigned short WORD;
//		struct {
//			unsigned short RCNT:1;
//			unsigned short REW:1;
//			unsigned short DCLRM:1;
//			unsigned short DREQE:1;
//			unsigned short :1;
//			unsigned short MBW:1;
//			unsigned short :1;
//			unsigned short BIGEND:1;
//			unsigned short :4;
//			unsigned short CURPIPE:4;
//		} BIT;
	} D0FIFOSEL;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BVAL:1;
//			unsigned short BCLR:1;
//			unsigned short FRDY:1;
//			unsigned short :4;
//			unsigned short DTLN:9;
//		} BIT;
	} D0FIFOCTR;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short RCNT:1;
//			unsigned short REW:1;
//			unsigned short DCLRM:1;
//			unsigned short DREQE:1;
//			unsigned short :1;
//			unsigned short MBW:1;
//			unsigned short :1;
//			unsigned short BIGEND:1;
//			unsigned short :4;
//			unsigned short CURPIPE:4;
//		} BIT;
	} D1FIFOSEL;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BVAL:1;
//			unsigned short BCLR:1;
//			unsigned short FRDY:1;
//			unsigned short :4;
//			unsigned short DTLN:9;
//		} BIT;
	} D1FIFOCTR;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short VBSE:1;
//			unsigned short RSME:1;
//			unsigned short SOFE:1;
//			unsigned short DVSE:1;
//			unsigned short CTRE:1;
//			unsigned short BEMPE:1;
//			unsigned short NRDYE:1;
//			unsigned short BRDYE:1;
//		} BIT;
	} INTENB0;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short OVRCRE:1;
//			unsigned short BCHGE:1;
//			unsigned short :1;
//			unsigned short DTCHE:1;
//			unsigned short ATTCHE:1;
//			unsigned short :4;
//			unsigned short EOFERRE:1;
//			unsigned short SIGNE:1;
//			unsigned short SACKE:1;
//		} BIT;
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
			unsigned short PIPE9NRDYE:1;
			unsigned short PIPE8NRDYE:1;
			unsigned short PIPE7NRDYE:1;
			unsigned short PIPE6NRDYE:1;
			unsigned short PIPE5NRDYE:1;
			unsigned short PIPE4NRDYE:1;
			unsigned short PIPE3NRDYE:1;
			unsigned short PIPE2NRDYE:1;
			unsigned short PIPE1NRDYE:1;
			unsigned short PIPE0NRDYE:1;
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
//		struct {
//			unsigned short :7;
//			unsigned short TRNENSEL:1;
//			unsigned short :1;
//			unsigned short BRDYM:1;
//			unsigned short :1;
//			unsigned short EDGESTS:1;
//		} BIT;
	} SOFCFG;
	char           wk8[2];
	union {
		unsigned short WORD;
//		struct {
//			unsigned short VBINT:1;
//			unsigned short RESM:1;
//			unsigned short SOFR:1;
//			unsigned short DVST:1;
//			unsigned short CTRT:1;
//			unsigned short BEMP:1;
//			unsigned short NRDY:1;
//			unsigned short BRDY:1;
//			unsigned short VBSTS:1;
//			unsigned short DVSQ:3;
//			unsigned short VALID:1;
//			unsigned short CTSQ:3;
//		} BIT;
	} INTSTS0;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short OVRCR:1;
//			unsigned short BCHG:1;
//			unsigned short :1;
//			unsigned short DTCH:1;
//			unsigned short ATTCH:1;
//			unsigned short :4;
//			unsigned short EOFERR:1;
//			unsigned short SIGN:1;
//			unsigned short SACK:1;
//		} BIT;
	} INTSTS1;
	char           wk9[2];
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :6;
//			unsigned short PIPE9BRDY:1;
//			unsigned short PIPE8BRDY:1;
//			unsigned short PIPE7BRDY:1;
//			unsigned short PIPE6BRDY:1;
//			unsigned short PIPE5BRDY:1;
//			unsigned short PIPE4BRDY:1;
//			unsigned short PIPE3BRDY:1;
//			unsigned short PIPE2BRDY:1;
//			unsigned short PIPE1BRDY:1;
//			unsigned short PIPE0BRDY:1;
//		} BIT;
	} BRDYSTS;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :6;
//			unsigned short PIPE9NRDY:1;
//			unsigned short PIPE8NRDY:1;
//			unsigned short PIPE7NRDY:1;
//			unsigned short PIPE6NRDY:1;
//			unsigned short PIPE5NRDY:1;
//			unsigned short PIPE4NRDY:1;
//			unsigned short PIPE3NRDY:1;
//			unsigned short PIPE2NRDY:1;
//			unsigned short PIPE1NRDY:1;
//			unsigned short PIPE0NRDY:1;
//		} BIT;
	} NRDYSTS;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :6;
//			unsigned short PIPE9BEMP:1;
//			unsigned short PIPE8BEMP:1;
//			unsigned short PIPE7BEMP:1;
//			unsigned short PIPE6BEMP:1;
//			unsigned short PIPE5BEMP:1;
//			unsigned short PIPE4BEMP:1;
//			unsigned short PIPE3BEMP:1;
//			unsigned short PIPE2BEMP:1;
//			unsigned short PIPE1BEMP:1;
//			unsigned short PIPE0BEMP:1;
//		} BIT;
	} BEMPSTS;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short OVRN:1;
//			unsigned short CRCE:1;
//			unsigned short :3;
//			unsigned short FRNM:11;
//		} BIT;
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
//		struct {
//			unsigned short :8;
//			unsigned short SHTNAK:1;
//			unsigned short :2;
//			unsigned short DIR:1;
//		} BIT;
	} DCPCFG;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short DEVSEL:4;
//			unsigned short :5;
//			unsigned short MXPS:7;
//		} BIT;
	} DCPMAXP;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BSTS:1;
//			unsigned short SUREQ:1;
//			unsigned short :2;
//			unsigned short SUREQCLR:1;
//			unsigned short :2;
//			unsigned short SQCLR:1;
//			unsigned short SQSET:1;
//			unsigned short SQMON:1;
//			unsigned short PBUSY:1;
//			unsigned short :2;
//			unsigned short CCPL:1;
//			unsigned short PID:2;
//		} BIT;
	} DCPCTR;
	char           wk11[2];
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :12;
//			unsigned short PIPESEL:4;
//		} BIT;
	} PIPESEL;
	char           wk12[2];
	union {
		unsigned short WORD;
//		struct {
//			unsigned short TYPE:2;
//			unsigned short :3;
//			unsigned short BFRE:1;
//			unsigned short DBLB:1;
//			unsigned short :1;
//			unsigned short SHTNAK:1;
//			unsigned short :2;
//			unsigned short DIR:1;
//			unsigned short EPNUM:4;
//		} BIT;
	} PIPECFG;
	char           wk13[2];
	union {
		unsigned short WORD;
//		struct {
//			unsigned short DEVSEL:4;
//			unsigned short :3;
//			unsigned short MXPS:9;
//		} BIT;
	} PIPEMAXP;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :3;
//			unsigned short IFIS:1;
//			unsigned short :9;
//			unsigned short IITV:3;
//		} BIT;
	} PIPEPERI;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BSTS:1;
//			unsigned short INBUFM:1;
//			unsigned short :3;
//			unsigned short ATREPM:1;
//			unsigned short ACLRM:1;
//			unsigned short SQCLR:1;
//			unsigned short SQSET:1;
//			unsigned short SQMON:1;
//			unsigned short PBUSY:1;
//			unsigned short :3;
//			unsigned short PID:2;
//		} BIT;
	} PIPE1CTR;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BSTS:1;
//			unsigned short INBUFM:1;
//			unsigned short :3;
//			unsigned short ATREPM:1;
//			unsigned short ACLRM:1;
//			unsigned short SQCLR:1;
//			unsigned short SQSET:1;
//			unsigned short SQMON:1;
//			unsigned short PBUSY:1;
//			unsigned short :3;
//			unsigned short PID:2;
//		} BIT;
	} PIPE2CTR;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BSTS:1;
//			unsigned short INBUFM:1;
//			unsigned short :3;
//			unsigned short ATREPM:1;
//			unsigned short ACLRM:1;
//			unsigned short SQCLR:1;
//			unsigned short SQSET:1;
//			unsigned short SQMON:1;
//			unsigned short PBUSY:1;
//			unsigned short :3;
//			unsigned short PID:2;
//		} BIT;
	} PIPE3CTR;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BSTS:1;
//			unsigned short INBUFM:1;
//			unsigned short :3;
//			unsigned short ATREPM:1;
//			unsigned short ACLRM:1;
//			unsigned short SQCLR:1;
//			unsigned short SQSET:1;
//			unsigned short SQMON:1;
//			unsigned short PBUSY:1;
//			unsigned short :3;
//			unsigned short PID:2;
//		} BIT;
	} PIPE4CTR;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BSTS:1;
//			unsigned short INBUFM:1;
//			unsigned short :3;
//			unsigned short ATREPM:1;
//			unsigned short ACLRM:1;
//			unsigned short SQCLR:1;
//			unsigned short SQSET:1;
//			unsigned short SQMON:1;
//			unsigned short PBUSY:1;
//			unsigned short :3;
//			unsigned short PID:2;
//		} BIT;
	} PIPE5CTR;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BSTS:1;
//			unsigned short :5;
//			unsigned short ACLRM:1;
//			unsigned short SQCLR:1;
//			unsigned short SQSET:1;
//			unsigned short SQMON:1;
//			unsigned short PBUSY:1;
//			unsigned short :3;
//			unsigned short PID:2;
//		} BIT;
	} PIPE6CTR;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BSTS:1;
//			unsigned short :5;
//			unsigned short ACLRM:1;
//			unsigned short SQCLR:1;
//			unsigned short SQSET:1;
//			unsigned short SQMON:1;
//			unsigned short PBUSY:1;
//			unsigned short :3;
//			unsigned short PID:2;
//		} BIT;
	} PIPE7CTR;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BSTS:1;
//			unsigned short :5;
//			unsigned short ACLRM:1;
//			unsigned short SQCLR:1;
//			unsigned short SQSET:1;
//			unsigned short SQMON:1;
//			unsigned short PBUSY:1;
//			unsigned short :3;
//			unsigned short PID:2;
//		} BIT;
	} PIPE8CTR;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BSTS:1;
//			unsigned short :5;
//			unsigned short ACLRM:1;
//			unsigned short SQCLR:1;
//			unsigned short SQSET:1;
//			unsigned short SQMON:1;
//			unsigned short PBUSY:1;
//			unsigned short :3;
//			unsigned short PID:2;
//		} BIT;
	} PIPE9CTR;
	char           wk14[14];
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :6;
//			unsigned short TRENB:1;
//			unsigned short TRCLR:1;
//		} BIT;
	} PIPE1TRE;
	unsigned short PIPE1TRN;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :6;
//			unsigned short TRENB:1;
//			unsigned short TRCLR:1;
//		} BIT;
	} PIPE2TRE;
	unsigned short PIPE2TRN;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :6;
//			unsigned short TRENB:1;
//			unsigned short TRCLR:1;
//		} BIT;
	} PIPE3TRE;
	unsigned short PIPE3TRN;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :6;
//			unsigned short TRENB:1;
//			unsigned short TRCLR:1;
//		} BIT;
	} PIPE4TRE;
	unsigned short PIPE4TRN;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :6;
//			unsigned short TRENB:1;
//			unsigned short TRCLR:1;
//		} BIT;
	} PIPE5TRE;
	unsigned short PIPE5TRN;
	char           wk15[44];
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :8;
//			unsigned short USBSPD:2;
//		} BIT;
	} DEVADD0;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :8;
//			unsigned short USBSPD:2;
//		} BIT;
	} DEVADD1;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :8;
//			unsigned short USBSPD:2;
//		} BIT;
	} DEVADD2;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :8;
//			unsigned short USBSPD:2;
//		} BIT;
	} DEVADD3;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :8;
//			unsigned short USBSPD:2;
//		} BIT;
	} DEVADD4;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :8;
//			unsigned short USBSPD:2;
//		} BIT;
	} DEVADD5;
	char           wk16[20];
	union {
		unsigned long LONG;
		struct {
			unsigned long :28;
			unsigned long SLEWF01:1;
			unsigned long SLEWF00:1;
			unsigned long SLEWR01:1;
			unsigned long SLEWR00:1;
		} BIT;
	} PHYSLEW;
};

struct st_usba {
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :7;
//			unsigned short CNEN:1;
//			unsigned short HSE:1;
//			unsigned short DCFM:1;
//			unsigned short DRPD:1;
//			unsigned short DPRPU:1;
//			unsigned short :3;
//			unsigned short USBE:1;
//		} BIT;
	} SYSCFG;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :12;
//			unsigned short BWAIT:4;
//		} BIT;
	} BUSWAIT;
	union {
		unsigned short WORD;
		struct {
			unsigned short OVCMON:2;
			unsigned short :7;
			unsigned short HTACT:1;
			unsigned short SOFEA:1;
			unsigned short :2;
			unsigned short IDMON:1;
			unsigned short LNST:2;
		} BIT;
	} SYSSTS0;
	union {
		unsigned short WORD;
		struct {
			unsigned short :15;
			unsigned short PLLLOCK:1;
		} BIT;
	} PLLSTA;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :4;
//			unsigned short HNPBTOA:1;
//			unsigned short EXICEN:1;
//			unsigned short VBUSEN:1;
//			unsigned short WKUP:1;
//			unsigned short RWUPE:1;
//			unsigned short USBRST:1;
//			unsigned short RESUME:1;
//			unsigned short UACT:1;
//			unsigned short :1;
//			unsigned short RHST:3;
//		} BIT;
	} DVSTCTR0;
	char           wk0[2];
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :12;
//			unsigned short UTST:4;
//		} BIT;
	} TESTMODE;
	char           wk1[6];
	union {
		unsigned long LONG;
		struct {
			unsigned short L;
			unsigned short H;
		} WORD;
		struct {
			unsigned char LL;
			unsigned char LH;
			unsigned char HL;
			unsigned char HH;
		} BYTE;
	} CFIFO;
	union {
		unsigned long LONG;
		struct {
			unsigned short L;
			unsigned short H;
		} WORD;
		struct {
			unsigned char LL;
			unsigned char LH;
			unsigned char HL;
			unsigned char HH;
		} BYTE;
	} D0FIFO;
	union {
		unsigned long LONG;
		struct {
			unsigned short L;
			unsigned short H;
		} WORD;
		struct {
			unsigned char LL;
			unsigned char LH;
			unsigned char HL;
			unsigned char HH;
		} BYTE;
	} D1FIFO;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short RCNT:1;
//			unsigned short REW:1;
//			unsigned short :2;
//			unsigned short MBW:2;
//			unsigned short :1;
//			unsigned short BIGEND:1;
//			unsigned short :2;
//			unsigned short ISEL:1;
//			unsigned short :1;
//			unsigned short CURPIPE:4;
//		} BIT;
	} CFIFOSEL;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BVAL:1;
//			unsigned short BCLR:1;
//			unsigned short FRDY:1;
//			unsigned short :1;
//			unsigned short DTLN:12;
//		} BIT;
	} CFIFOCTR;
	char           wk2[4];
	union {
		unsigned short WORD;
//		struct {
//			unsigned short RCNT:1;
//			unsigned short REW:1;
//			unsigned short DCLRM:1;
//			unsigned short DREQE:1;
//			unsigned short MBW:2;
//			unsigned short :1;
//			unsigned short BIGEND:1;
//			unsigned short :4;
//			unsigned short CURPIPE:4;
//		} BIT;
	} D0FIFOSEL;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BVAL:1;
//			unsigned short BCLR:1;
//			unsigned short FRDY:1;
//			unsigned short :1;
//			unsigned short DTLN:12;
//		} BIT;
	} D0FIFOCTR;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short RCNT:1;
//			unsigned short REW:1;
//			unsigned short DCLRM:1;
//			unsigned short DREQE:1;
//			unsigned short MBW:2;
//			unsigned short :1;
//			unsigned short BIGEND:1;
//			unsigned short :4;
//			unsigned short CURPIPE:4;
//		} BIT;
	} D1FIFOSEL;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BVAL:1;
//			unsigned short BCLR:1;
//			unsigned short FRDY:1;
//			unsigned short :1;
//			unsigned short DTLN:12;
//		} BIT;
	} D1FIFOCTR;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short VBSE:1;
//			unsigned short RSME:1;
//			unsigned short SOFE:1;
//			unsigned short DVSE:1;
//			unsigned short CTRE:1;
//			unsigned short BEMPE:1;
//			unsigned short NRDYE:1;
//			unsigned short BRDYE:1;
//		} BIT;
	} INTENB0;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short OVRCRE:1;
//			unsigned short BCHGE:1;
//			unsigned short :1;
//			unsigned short DTCHE:1;
//			unsigned short ATTCHE:1;
//			unsigned short :1;
//			unsigned short L1RSMENDE:1;
//			unsigned short LPMENDE:1;
//			unsigned short :1;
//			unsigned short EOFERRE:1;
//			unsigned short SIGNE:1;
//			unsigned short SACKE:1;
//			unsigned short :3;
//			unsigned short PDDETINTE:1;
//		} BIT;
	} INTENB1;
	char           wk3[2];
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
			unsigned short PIPE9NRDYE:1;
			unsigned short PIPE8NRDYE:1;
			unsigned short PIPE7NRDYE:1;
			unsigned short PIPE6NRDYE:1;
			unsigned short PIPE5NRDYE:1;
			unsigned short PIPE4NRDYE:1;
			unsigned short PIPE3NRDYE:1;
			unsigned short PIPE2NRDYE:1;
			unsigned short PIPE1NRDYE:1;
			unsigned short PIPE0NRDYE:1;
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
//		struct {
//			unsigned short :7;
//			unsigned short TRNENSEL:1;
//			unsigned short :1;
//			unsigned short BRDYM:1;
//			unsigned short INTL:1;
//			unsigned short EDGESTS:1;
//		} BIT;
	} SOFCFG;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short HSEB:1;
//			unsigned short :5;
//			unsigned short REPSEL:2;
//			unsigned short :2;
//			unsigned short CLKSEL:2;
//			unsigned short CDPEN:1;
//			unsigned short :1;
//			unsigned short PLLRESET:1;
//			unsigned short DIRPD:1;
//		} BIT;
	} PHYSET;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short VBINT:1;
//			unsigned short RESM:1;
//			unsigned short SOFR:1;
//			unsigned short DVST:1;
//			unsigned short CTRT:1;
//			unsigned short BEMP:1;
//			unsigned short NRDY:1;
//			unsigned short BRDY:1;
//			unsigned short VBSTS:1;
//			unsigned short DVSQ:3;
//			unsigned short VALID:1;
//			unsigned short CTSQ:3;
//		} BIT;
	} INTSTS0;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short OVRCR:1;
//			unsigned short BCHG:1;
//			unsigned short :1;
//			unsigned short DTCH:1;
//			unsigned short ATTCH:1;
//			unsigned short :1;
//			unsigned short L1RSMEND:1;
//			unsigned short LPMEND:1;
//			unsigned short :1;
//			unsigned short EOFERR:1;
//			unsigned short SIGN:1;
//			unsigned short SACK:1;
//			unsigned short :3;
//			unsigned short PDDETINT:1;
//		} BIT;
	} INTSTS1;
	char           wk4[2];
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :6;
//			unsigned short PIPEBRDY:10;
//		} BIT;
	} BRDYSTS;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :6;
//			unsigned short PIPENRDY:10;
//		} BIT;
	} NRDYSTS;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :6;
//			unsigned short PIPEBEMP:10;
//		} BIT;
	} BEMPSTS;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short OVRN:1;
//			unsigned short CRCE:1;
//			unsigned short :3;
//			unsigned short FRNM:11;
//		} BIT;
	} FRMNUM;
	union {
		unsigned short WORD;
		struct {
			unsigned short :13;
			unsigned short UFRNM:3;
		} BIT;
	} UFRMNUM;
	union {
		unsigned short WORD;
		struct {
			unsigned short :9;
			unsigned short USBADDR:7;
		} BIT;
	} USBADDR;
	char           wk5[2];
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
//		struct {
//			unsigned short :7;
//			unsigned short CNTMD:1;
//			unsigned short SHTNAK:1;
//			unsigned short :2;
//			unsigned short DIR:1;
//		} BIT;
	} DCPCFG;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short DEVSEL:4;
//			unsigned short :5;
//			unsigned short MXPS:7;
//		} BIT;
	} DCPMAXP;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BSTS:1;
//			unsigned short SUREQ:1;
//			unsigned short :2;
//			unsigned short SUREQCLR:1;
//			unsigned short :2;
//			unsigned short SQCLR:1;
//			unsigned short SQSET:1;
//			unsigned short SQMON:1;
//			unsigned short PBUSY:1;
//			unsigned short :2;
//			unsigned short CCPL:1;
//			unsigned short PID:2;
//		} BIT;
	} DCPCTR;
	char           wk6[2];
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :12;
//			unsigned short PIPESEL:4;
//		} BIT;
	} PIPESEL;
	char           wk7[2];
	union {
		unsigned short WORD;
//		struct {
//			unsigned short TYPE:2;
//			unsigned short :3;
//			unsigned short BFRE:1;
//			unsigned short DBLB:1;
//			unsigned short CNTMD:1;
//			unsigned short SHTNAK:1;
//			unsigned short :2;
//			unsigned short DIR:1;
//			unsigned short EPNUM:4;
//		} BIT;
	} PIPECFG;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :1;
//			unsigned short BUFSIZE:5;
//			unsigned short :2;
//			unsigned short BUFNMB:8;
//		} BIT;
	} PIPEBUF;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short DEVSEL:4;
//			unsigned short :1;
//			unsigned short MXPS:11;
//		} BIT;
	} PIPEMAXP;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :3;
//			unsigned short IFIS:1;
//			unsigned short :9;
//			unsigned short IITV:3;
//		} BIT;
	} PIPEPERI;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BSTS:1;
//			unsigned short INBUFM:1;
//			unsigned short :3;
//			unsigned short ATREPM:1;
//			unsigned short ACLRM:1;
//			unsigned short SQCLR:1;
//			unsigned short SQSET:1;
//			unsigned short SQMON:1;
//			unsigned short PBUSY:1;
//			unsigned short :3;
//			unsigned short PID:2;
//		} BIT;
	} PIPE1CTR;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BSTS:1;
//			unsigned short INBUFM:1;
//			unsigned short :3;
//			unsigned short ATREPM:1;
//			unsigned short ACLRM:1;
//			unsigned short SQCLR:1;
//			unsigned short SQSET:1;
//			unsigned short SQMON:1;
//			unsigned short PBUSY:1;
//			unsigned short :3;
//			unsigned short PID:2;
//		} BIT;
	} PIPE2CTR;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BSTS:1;
//			unsigned short INBUFM:1;
//			unsigned short :3;
//			unsigned short ATREPM:1;
//			unsigned short ACLRM:1;
//			unsigned short SQCLR:1;
//			unsigned short SQSET:1;
//			unsigned short SQMON:1;
//			unsigned short PBUSY:1;
//			unsigned short :3;
//			unsigned short PID:2;
//		} BIT;
	} PIPE3CTR;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BSTS:1;
//			unsigned short INBUFM:1;
//			unsigned short :3;
//			unsigned short ATREPM:1;
//			unsigned short ACLRM:1;
//			unsigned short SQCLR:1;
//			unsigned short SQSET:1;
//			unsigned short SQMON:1;
//			unsigned short PBUSY:1;
//			unsigned short :3;
//			unsigned short PID:2;
//		} BIT;
	} PIPE4CTR;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BSTS:1;
//			unsigned short INBUFM:1;
//			unsigned short :3;
//			unsigned short ATREPM:1;
//			unsigned short ACLRM:1;
//			unsigned short SQCLR:1;
//			unsigned short SQSET:1;
//			unsigned short SQMON:1;
//			unsigned short PBUSY:1;
//			unsigned short :3;
//			unsigned short PID:2;
//		} BIT;
	} PIPE5CTR;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BSTS:1;
//			unsigned short INBUFM:1;
//			unsigned short :3;
//			unsigned short ATREPM:1;
//			unsigned short ACLRM:1;
//			unsigned short SQCLR:1;
//			unsigned short SQSET:1;
//			unsigned short SQMON:1;
//			unsigned short PBUSY:1;
//			unsigned short :3;
//			unsigned short PID:2;
//		} BIT;
	} PIPE6CTR;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BSTS:1;
//			unsigned short INBUFM:1;
//			unsigned short :3;
//			unsigned short ATREPM:1;
//			unsigned short ACLRM:1;
//			unsigned short SQCLR:1;
//			unsigned short SQSET:1;
//			unsigned short SQMON:1;
//			unsigned short PBUSY:1;
//			unsigned short :3;
//			unsigned short PID:2;
//		} BIT;
	} PIPE7CTR;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BSTS:1;
//			unsigned short INBUFM:1;
//			unsigned short :3;
//			unsigned short ATREPM:1;
//			unsigned short ACLRM:1;
//			unsigned short SQCLR:1;
//			unsigned short SQSET:1;
//			unsigned short SQMON:1;
//			unsigned short PBUSY:1;
//			unsigned short :3;
//			unsigned short PID:2;
//		} BIT;
	} PIPE8CTR;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BSTS:1;
//			unsigned short INBUFM:1;
//			unsigned short :3;
//			unsigned short ATREPM:1;
//			unsigned short ACLRM:1;
//			unsigned short SQCLR:1;
//			unsigned short SQSET:1;
//			unsigned short SQMON:1;
//			unsigned short PBUSY:1;
//			unsigned short :3;
//			unsigned short PID:2;
//		} BIT;
	} PIPE9CTR;
	char           wk8[14];
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :6;
//			unsigned short TRENB:1;
//			unsigned short TRCLR:1;
//		} BIT;
	} PIPE1TRE;
	union {
		unsigned short WORD;
		struct {
			unsigned short TRNCNT:16;
		} BIT;
	} PIPE1TRN;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :6;
//			unsigned short TRENB:1;
//			unsigned short TRCLR:1;
//		} BIT;
	} PIPE2TRE;
	union {
		unsigned short WORD;
		struct {
			unsigned short TRNCNT:16;
		} BIT;
	} PIPE2TRN;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :6;
//			unsigned short TRENB:1;
//			unsigned short TRCLR:1;
//		} BIT;
	} PIPE3TRE;
	union {
		unsigned short WORD;
		struct {
			unsigned short TRNCNT:16;
		} BIT;
	} PIPE3TRN;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :6;
//			unsigned short TRENB:1;
//			unsigned short TRCLR:1;
//		} BIT;
	} PIPE4TRE;
	union {
		unsigned short WORD;
		struct {
			unsigned short TRNCNT:16;
		} BIT;
	} PIPE4TRN;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :6;
//			unsigned short TRENB:1;
//			unsigned short TRCLR:1;
//		} BIT;
	} PIPE5TRE;
	union {
		unsigned short WORD;
		struct {
			unsigned short TRNCNT:16;
		} BIT;
	} PIPE5TRN;
	char           wk9[44];
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :1;
//			unsigned short UPPHUB:4;
//			unsigned short HUBPORT:3;
//			unsigned short USBSPD:2;
//		} BIT;
	} DEVADD0;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :1;
//			unsigned short UPPHUB:4;
//			unsigned short HUBPORT:3;
//			unsigned short USBSPD:2;
//		} BIT;
	} DEVADD1;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :1;
//			unsigned short UPPHUB:4;
//			unsigned short HUBPORT:3;
//			unsigned short USBSPD:2;
//		} BIT;
	} DEVADD2;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :1;
//			unsigned short UPPHUB:4;
//			unsigned short HUBPORT:3;
//			unsigned short USBSPD:2;
//		} BIT;
	} DEVADD3;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :1;
//			unsigned short UPPHUB:4;
//			unsigned short HUBPORT:3;
//			unsigned short USBSPD:2;
//		} BIT;
	} DEVADD4;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :1;
//			unsigned short UPPHUB:4;
//			unsigned short HUBPORT:3;
//			unsigned short USBSPD:2;
//		} BIT;
	} DEVADD5;
	char           wk10[36];
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :8;
//			unsigned short HWUPM:1;
//		} BIT;
	} LPCTRL;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :1;
//			unsigned short SUSPENDM:1;
//		} BIT;
	} LPSTS;
	char           wk11[60];
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :6;
//			unsigned short PDDETSTS:1;
//			unsigned short CHGDETSTS:1;
//			unsigned short :3;
//			unsigned short VDMSRCE:1;
//			unsigned short IDPSINKE:1;
//			unsigned short VDPSRCE:1;
//			unsigned short IDMSINKE:1;
//			unsigned short IDPSRCE:1;
//		} BIT;
	} BCCTRL;
	char           wk12[2];
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :1;
//			unsigned short L1EXTMD:1;
//			unsigned short :2;
//			unsigned short HIRDTHR:4;
//			unsigned short DVSQ:4;
//			unsigned short L1NEGOMD:1;
//			unsigned short L1RESPMD:2;
//			unsigned short L1RESPEN:1;
//		} BIT;
	} PL1CTRL1;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :3;
//			unsigned short RWEMON:1;
//			unsigned short HIRDMON:4;
//		} BIT;
	} PL1CTRL2;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short :13;
//			unsigned short L1STATUS:2;
//			unsigned short L1REQ:1;
//		} BIT;
	} HL1CTRL1;
	union {
		unsigned short WORD;
//		struct {
//			unsigned short BESL:1;
//			unsigned short :2;
//			unsigned short L1RWE:1;
//			unsigned short HIRD:4;
//			unsigned short :4;
//			unsigned short L1ADDR:4;
//		} BIT;
	} HL1CTRL2;
	char           wk13[20];
	union {
		unsigned long LONG;
//		struct {
//			unsigned long :8;
//			unsigned long DVBSTSHM:1;
//			unsigned long :1;
//			unsigned long DOVCBHM:1;
//			unsigned long DOVCAHM:1;
//		} BIT;
	} DPUSR0R;
	union {
		unsigned long LONG;
//		struct {
//			unsigned long :8;
//			unsigned long DVBSTSH:1;
//			unsigned long :1;
//			unsigned long DOVCBH:1;
//			unsigned long DOVCAH:1;
//			unsigned long :12;
//			unsigned long DVBSTSHE:1;
//			unsigned long :1;
//			unsigned long DOVCBHE:1;
//			unsigned long DOVCAHE:1;
//		} BIT;
	} DPUSR1R;
};

struct st_wdt {
	unsigned char  WDTRR;
	char           wk0[1];
	union {
		unsigned short WORD;
		struct {
			unsigned short :2;
			unsigned short RPSS:2;
			unsigned short :2;
			unsigned short RPES:2;
			unsigned short CKS:4;
			unsigned short :2;
			unsigned short TOPS:2;
		} BIT;
	} WDTCR;
	union {
		unsigned short WORD;
		struct {
			unsigned short REFEF:1;
			unsigned short UNDFF:1;
			unsigned short CNTVAL:14;
		} BIT;
	} WDTSR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char RSTIRQS:1;
		} BIT;
	} WDTRCR;
};

enum enum_ir {
IR_BSC_BUSERR=16,IR_RAM_RAMERR=18,
IR_FCU_FIFERR=21,IR_FCU_FRDYI=23,
IR_ICU_SWINT2=26,IR_ICU_SWINT,
IR_CMT0_CMI0,
IR_CMT1_CMI1,
IR_CMTW0_CMWI0,
IR_CMTW1_CMWI1,
IR_USBA_D0FIFO2,IR_USBA_D1FIFO2,
IR_USB0_D0FIFO0,IR_USB0_D1FIFO0,
IR_RSPI0_SPRI0=38,IR_RSPI0_SPTI0,
IR_RSPI1_SPRI1,IR_RSPI1_SPTI1,
IR_QSPI_SPRI=42,IR_QSPI_SPTI,
IR_SDHI_SBFAI,
IR_MMCIF_MBFAI,
IR_SSI0_SSITXI0,IR_SSI0_SSIRXI0,
IR_SSI1_SSIRTI1,
IR_SRC_IDEI=50,IR_SRC_ODFI,
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
IR_USBA_USBAR,
IR_IWDT_IWUNI,
IR_WDT_WUNI,
IR_PDC_PCDFI,
IR_SCI7_RXI7,IR_SCI7_TXI7,
IR_SCIFA8_RXIF8,IR_SCIFA8_TXIF8,
IR_SCIFA9_RXIF9,IR_SCIFA9_TXIF9,
IR_SCIFA10_RXIF10,IR_SCIFA10_TXIF10,
IR_ICU_GROUPBE0,IR_ICU_GROUPBL0=110,IR_ICU_GROUPBL1,IR_ICU_GROUPAL0,IR_ICU_GROUPAL1,
IR_SCIFA11_RXIF11,IR_SCIFA11_TXIF11,
IR_SCI12_RXI12,IR_SCI12_TXI12,
IR_DMAC_DMAC0I=120,IR_DMAC_DMAC1I,IR_DMAC_DMAC2I,IR_DMAC_DMAC3I,IR_DMAC_DMAC74I,
IR_OST_OST,
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
};

enum enum_dtce {
DTCE_ICU_SWINT2=26,DTCE_ICU_SWINT,
DTCE_CMT0_CMI0,
DTCE_CMT1_CMI1,
DTCE_CMTW0_CMWI0,
DTCE_CMTW1_CMWI1,
DTCE_USBA_D0FIFO2,DTCE_USBA_D1FIFO2,
DTCE_USB0_D0FIFO0,DTCE_USB0_D1FIFO0,
DTCE_RSPI0_SPRI0=38,DTCE_RSPI0_SPTI0,
DTCE_RSPI1_SPRI1,DTCE_RSPI1_SPTI1,
DTCE_QSPI_SPRI=42,DTCE_QSPI_SPTI,
DTCE_SDHI_SBFAI,
DTCE_MMCIF_MBFAI,
DTCE_SSI0_SSITXI0,DTCE_SSI0_SSIRXI0,
DTCE_SSI1_SSIRTI1,
DTCE_SRC_IDEI=50,DTCE_SRC_ODFI,
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
DTCE_SCIFA8_RXIF8,DTCE_SCIFA8_TXIF8,
DTCE_SCIFA9_RXIF9,DTCE_SCIFA9_TXIF9,
DTCE_SCIFA10_RXIF10,DTCE_SCIFA10_TXIF10,
DTCE_SCIFA11_RXIF11=114,DTCE_SCIFA11_TXIF11,
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
};

enum enum_ier {
IER_BSC_BUSERR=0x02,
IER_RAM_RAMERR=0x02,
IER_FCU_FIFERR=0x02,IER_FCU_FRDYI=0x02,
IER_ICU_SWINT2=0x03,IER_ICU_SWINT=0x03,
IER_CMT0_CMI0=0x03,
IER_CMT1_CMI1=0x03,
IER_CMTW0_CMWI0=0x03,
IER_CMTW1_CMWI1=0x03,
IER_USBA_D0FIFO2=0x04,IER_USBA_D1FIFO2=0x04,
IER_USB0_D0FIFO0=0x04,IER_USB0_D1FIFO0=0x04,
IER_RSPI0_SPRI0=0x04,IER_RSPI0_SPTI0=0x04,
IER_RSPI1_SPRI1=0x05,IER_RSPI1_SPTI1=0x05,
IER_QSPI_SPRI=0x05,IER_QSPI_SPTI=0x05,
IER_SDHI_SBFAI=0x05,
IER_MMCIF_MBFAI=0x05,
IER_SSI0_SSITXI0=0x05,IER_SSI0_SSIRXI0=0x05,
IER_SSI1_SSIRTI1=0x06,
IER_SRC_IDEI=0x06,IER_SRC_ODFI=0x06,
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
IER_USBA_USBAR=0x0B,
IER_IWDT_IWUNI=0x0B,
IER_WDT_WUNI=0x0C,
IER_PDC_PCDFI=0x0C,
IER_SCI7_RXI7=0x0C,IER_SCI7_TXI7=0x0C,
IER_SCIFA8_RXIF8=0x0C,IER_SCIFA8_TXIF8=0x0C,
IER_SCIFA9_RXIF9=0x0C,IER_SCIFA9_TXIF9=0x0C,
IER_SCIFA10_RXIF10=0x0D,IER_SCIFA10_TXIF10=0x0D,
IER_ICU_GROUPBE0=0x0D,IER_ICU_GROUPBL0=0x0D,IER_ICU_GROUPBL1=0x0D,IER_ICU_GROUPAL0=0x0E,IER_ICU_GROUPAL1=0x0E,
IER_SCIFA11_RXIF11=0x0E,IER_SCIFA11_TXIF11=0x0E,
IER_SCI12_RXI12=0x0E,IER_SCI12_TXI12=0x0E,
IER_DMAC_DMAC0I=0x0F,IER_DMAC_DMAC1I=0x0F,IER_DMAC_DMAC2I=0x0F,IER_DMAC_DMAC3I=0x0F,IER_DMAC_DMAC74I=0x0F,
IER_OST_OST=0x0F,
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
};

enum enum_ipr {
IPR_BSC_BUSERR=0,
IPR_RAM_RAMERR=0,
IPR_FCU_FIFERR=1,IPR_FCU_FRDYI=2,
IPR_ICU_SWINT2=3,IPR_ICU_SWINT=3,
IPR_CMT0_CMI0=4,
IPR_CMT1_CMI1=5,
IPR_CMTW0_CMWI0=6,
IPR_CMTW1_CMWI1=7,
IPR_USBA_D0FIFO2=32,IPR_USBA_D1FIFO2=33,
IPR_USB0_D0FIFO0=34,IPR_USB0_D1FIFO0=35,
IPR_RSPI0_SPRI0=38,IPR_RSPI0_SPTI0=39,
IPR_RSPI1_SPRI1=40,IPR_RSPI1_SPTI1=41,
IPR_QSPI_SPRI=42,IPR_QSPI_SPTI=43,
IPR_SDHI_SBFAI=44,
IPR_MMCIF_MBFAI=45,
IPR_SSI0_SSITXI0=46,IPR_SSI0_SSIRXI0=47,
IPR_SSI1_SSIRTI1=48,
IPR_SRC_IDEI=50,IPR_SRC_ODFI=51,
IPR_RIIC0_RXI0=52,IPR_RIIC0_TXI0=53,
IPR_RIIC2_RXI2=54,IPR_RIIC2_TXI2=55,
IPR_SCI0_RXI0=58,IPR_SCI0_TXI0=59,
IPR_SCI1_RXI1=60,IPR_SCI1_TXI1=61,
IPR_SCI2_RXI2=62,IPR_SCI2_TXI2=63,
IPR_ICU_IRQ0=64,IPR_ICU_IRQ1=65,IPR_ICU_IRQ2=66,IPR_ICU_IRQ3=67,IPR_ICU_IRQ4=68,IPR_ICU_IRQ5=69,IPR_ICU_IRQ6=70,IPR_ICU_IRQ7=71,IPR_ICU_IRQ8=72,IPR_ICU_IRQ9=73,IPR_ICU_IRQ10=74,IPR_ICU_IRQ11=75,IPR_ICU_IRQ12=76,IPR_ICU_IRQ13=77,IPR_ICU_IRQ14=78,IPR_ICU_IRQ15=79,
IPR_SCI3_RXI3=80,IPR_SCI3_TXI3=81,
IPR_SCI4_RXI4=82,IPR_SCI4_TXI4=83,
IPR_SCI5_RXI5=84,IPR_SCI5_TXI5=85,
IPR_SCI6_RXI6=86,IPR_SCI6_TXI6=87,
IPR_LVD1_LVD1=88,
IPR_LVD2_LVD2=89,
IPR_USB0_USBR0=90,
IPR_RTC_ALM=92,IPR_RTC_PRD=93,
IPR_USBA_USBAR=94,
IPR_IWDT_IWUNI=95,
IPR_WDT_WUNI=96,
IPR_PDC_PCDFI=97,
IPR_SCI7_RXI7=98,IPR_SCI7_TXI7=99,
IPR_SCIFA8_RXIF8=100,IPR_SCIFA8_TXIF8=101,
IPR_SCIFA9_RXIF9=102,IPR_SCIFA9_TXIF9=103,
IPR_SCIFA10_RXIF10=104,IPR_SCIFA10_TXIF10=105,
IPR_ICU_GROUPBE0=106,IPR_ICU_GROUPBL0=110,IPR_ICU_GROUPBL1=111,IPR_ICU_GROUPAL0=112,IPR_ICU_GROUPAL1=113,
IPR_SCIFA11_RXIF11=114,IPR_SCIFA11_TXIF11=115,
IPR_SCI12_RXI12=116,IPR_SCI12_TXI12=117,
IPR_DMAC_DMAC0I=120,IPR_DMAC_DMAC1I=121,IPR_DMAC_DMAC2I=122,IPR_DMAC_DMAC3I=123,IPR_DMAC_DMAC74I=124,
IPR_OST_OST=125,
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
IPR_PERIA_INTA253=253,IPR_PERIA_INTA254=254,IPR_PERIA_INTA255=255
};

#define	IEN_BSC_BUSERR		IEN0
#define	IEN_RAM_RAMERR		IEN2
#define	IEN_FCU_FIFERR		IEN5
#define	IEN_FCU_FRDYI		IEN7
#define	IEN_ICU_SWINT2		IEN2
#define	IEN_ICU_SWINT		IEN3
#define	IEN_CMT0_CMI0		IEN4
#define	IEN_CMT1_CMI1		IEN5
#define	IEN_CMTW0_CMWI0		IEN6
#define	IEN_CMTW1_CMWI1		IEN7
#define	IEN_USBA_D0FIFO2	IEN0
#define	IEN_USBA_D1FIFO2	IEN1
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
#define	IEN_SSI0_SSITXI0	IEN6
#define	IEN_SSI0_SSIRXI0	IEN7
#define	IEN_SSI1_SSIRTI1	IEN0
#define	IEN_SRC_IDEI		IEN2
#define	IEN_SRC_ODFI		IEN3
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
#define	IEN_USBA_USBAR	IEN6
#define	IEN_IWDT_IWUNI		IEN7
#define	IEN_WDT_WUNI		IEN0
#define	IEN_PDC_PCDFI		IEN1
#define	IEN_SCI7_RXI7		IEN2
#define	IEN_SCI7_TXI7		IEN3
#define	IEN_SCIFA8_RXIF8	IEN4
#define	IEN_SCIFA8_TXIF8	IEN5
#define	IEN_SCIFA9_RXIF9	IEN6
#define	IEN_SCIFA9_TXIF9	IEN7
#define	IEN_SCIFA10_RXIF10	IEN0
#define	IEN_SCIFA10_TXIF10	IEN1
#define	IEN_ICU_GROUPBE0	IEN2
#define	IEN_ICU_GROUPBL0	IEN6
#define	IEN_ICU_GROUPBL1	IEN7
#define	IEN_ICU_GROUPAL0	IEN0
#define	IEN_ICU_GROUPAL1	IEN1
#define	IEN_SCIFA11_RXIF11	IEN2
#define	IEN_SCIFA11_TXIF11	IEN3
#define	IEN_SCI12_RXI12		IEN4
#define	IEN_SCI12_TXI12		IEN5
#define	IEN_DMAC_DMAC0I		IEN0
#define	IEN_DMAC_DMAC1I		IEN1
#define	IEN_DMAC_DMAC2I		IEN2
#define	IEN_DMAC_DMAC3I		IEN3
#define	IEN_DMAC_DMAC74I	IEN4
#define	IEN_OST_OST			IEN5
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
#define	VECT_RAM_RAMERR		18
#define	VECT_FCU_FIFERR		21
#define	VECT_FCU_FRDYI		23
#define	VECT_ICU_SWINT2		26
#define	VECT_ICU_SWINT		27
#define	VECT_CMT0_CMI0		28
#define	VECT_CMT1_CMI1		29
#define	VECT_CMTW0_CMWI0	30
#define	VECT_CMTW1_CMWI1	31
#define	VECT_USBA_D0FIFO2	32
#define	VECT_USBA_D1FIFO2	33
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
#define	VECT_SSI0_SSITXI0	46
#define	VECT_SSI0_SSIRXI0	47
#define	VECT_SSI1_SSIRTI1	48
#define	VECT_SRC_IDEI		50
#define	VECT_SRC_ODFI		51
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
#define	VECT_USBA_USBAR		94
#define	VECT_IWDT_IWUNI		95
#define	VECT_WDT_WUNI		96
#define	VECT_PDC_PCDFI		97
#define	VECT_SCI7_RXI7		98
#define	VECT_SCI7_TXI7		99
#define	VECT_SCIFA8_RXIF8	100
#define	VECT_SCIFA8_TXIF8	101
#define	VECT_SCIFA9_RXIF9	102
#define	VECT_SCIFA9_TXIF9	103
#define	VECT_SCIFA10_RXIF10	104
#define	VECT_SCIFA10_TXIF10	105
#define	VECT_ICU_GROUPBE0	106
#define	VECT_ICU_GROUPBL0	110
#define	VECT_ICU_GROUPBL1	111
#define	VECT_ICU_GROUPAL0	112
#define	VECT_ICU_GROUPAL1	113
#define	VECT_SCIFA11_RXIF11	114
#define	VECT_SCIFA11_TXIF11	115
#define	VECT_SCI12_RXI12	116
#define	VECT_SCI12_TXI12	117
#define	VECT_DMAC_DMAC0I	120
#define	VECT_DMAC_DMAC1I	121
#define	VECT_DMAC_DMAC2I	122
#define	VECT_DMAC_DMAC3I	123
#define	VECT_DMAC_DMAC74I	124
#define	VECT_OST_OST		125
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
#define	MSTP_GPT		SYSTEM.MSTPCRA.BIT.MSTPA7
#define	MSTP_GPT0		SYSTEM.MSTPCRA.BIT.MSTPA7
#define	MSTP_GPT1		SYSTEM.MSTPCRA.BIT.MSTPA7
#define	MSTP_GPT2		SYSTEM.MSTPCRA.BIT.MSTPA7
#define	MSTP_GPT3		SYSTEM.MSTPCRA.BIT.MSTPA7
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
#define	MSTP_USB0		SYSTEM.MSTPCRB.BIT.MSTPB19
#define	MSTP_RSPI0		SYSTEM.MSTPCRB.BIT.MSTPB17
#define	MSTP_RSPI1		SYSTEM.MSTPCRB.BIT.MSTPB16
#define	MSTP_EDMAC0		SYSTEM.MSTPCRB.BIT.MSTPB15
#define	MSTP_EDMAC1		SYSTEM.MSTPCRB.BIT.MSTPB14
#define	MSTP_USBA		SYSTEM.MSTPCRB.BIT.MSTPB12
#define	MSTP_ELC		SYSTEM.MSTPCRB.BIT.MSTPB9
#define	MSTP_TEMPS		SYSTEM.MSTPCRB.BIT.MSTPB8
#define	MSTP_DOC		SYSTEM.MSTPCRB.BIT.MSTPB6
#define	MSTP_SCI12		SYSTEM.MSTPCRB.BIT.MSTPB4
#define	MSTP_SMCI12		SYSTEM.MSTPCRB.BIT.MSTPB4
#define	MSTP_CAN2		SYSTEM.MSTPCRB.BIT.MSTPB2
#define	MSTP_CAN1		SYSTEM.MSTPCRB.BIT.MSTPB1
#define	MSTP_CAN0		SYSTEM.MSTPCRB.BIT.MSTPB0
#define	MSTP_SCIFA8		SYSTEM.MSTPCRC.BIT.MSTPC27
#define	MSTP_SCIFA9		SYSTEM.MSTPCRC.BIT.MSTPC26
#define	MSTP_SCIFA10	SYSTEM.MSTPCRC.BIT.MSTPC25
#define	MSTP_SCIFA11	SYSTEM.MSTPCRC.BIT.MSTPC24
#define	MSTP_QSPI		SYSTEM.MSTPCRC.BIT.MSTPC23
#define	MSTP_CAC		SYSTEM.MSTPCRC.BIT.MSTPC19
#define	MSTP_RIIC2		SYSTEM.MSTPCRC.BIT.MSTPC17
#define	MSTP_STBYRAM	SYSTEM.MSTPCRC.BIT.MSTPC7
#define	MSTP_ECCRAM		SYSTEM.MSTPCRC.BIT.MSTPC6
#define	MSTP_RAM0		SYSTEM.MSTPCRC.BIT.MSTPC0
#define	MSTP_SRC		SYSTEM.MSTPCRD.BIT.MSTPD23
#define	MSTP_MMCIF		SYSTEM.MSTPCRD.BIT.MSTPD21
#define	MSTP_SDHI		SYSTEM.MSTPCRD.BIT.MSTPD19
#define	MSTP_SSI0		SYSTEM.MSTPCRD.BIT.MSTPD15
#define	MSTP_SSI1		SYSTEM.MSTPCRD.BIT.MSTPD14

#define	IS_CAN0_ERS0		IS0
#define	IS_CAN1_ERS1		IS1
#define	IS_CAN2_ERS2		IS2
#define	IS_SCI0_TEI0		IS0
#define	IS_SCI0_ERI0		IS1
#define	IS_SCI1_TEI1		IS2
#define	IS_SCI1_ERI1		IS3
#define	IS_SCI2_TEI2		IS4
#define	IS_SCI2_ERI2		IS5
#define	IS_SCI3_TEI3		IS6
#define	IS_SCI3_ERI3		IS7
#define	IS_SCI4_TEI4		IS8
#define	IS_SCI4_ERI4		IS9
#define	IS_SCI5_TEI5		IS10
#define	IS_SCI5_ERI5		IS11
#define	IS_SCI6_TEI6		IS12
#define	IS_SCI6_ERI6		IS13
#define	IS_SCI7_TEI7		IS14
#define	IS_SCI7_ERI7		IS15
#define	IS_SCI12_TEI12		IS16
#define	IS_SCI12_ERI12		IS17
#define	IS_SCI12_SCIX0		IS18
#define	IS_SCI12_SCIX1		IS19
#define	IS_SCI12_SCIX2		IS20
#define	IS_SCI12_SCIX3		IS21
#define	IS_QSPI_QSPSSLI		IS24
#define	IS_CAC_FERRF		IS26
#define	IS_CAC_MENDF		IS27
#define	IS_CAC_OVFF			IS28
#define	IS_DOC_DOPCF		IS29
#define	IS_PDC_PCFEI		IS30
#define	IS_PDC_PCERI		IS31
#define	IS_SRC_PCERI		IS0
#define	IS_SRC_OVF			IS1
#define	IS_SRC_CEF			IS2
#define	IS_SDHI_CDETI		IS3
#define	IS_SDHI_CACI		IS4
#define	IS_SDHI_SDACI		IS5
#define	IS_MMCIF_CDETIO		IS6
#define	IS_MMCIF_ERRIO		IS7
#define	IS_MMCIF_ACCIO		IS8
#define	IS_POE3_OEI1		IS9
#define	IS_POE3_OEI2		IS10
#define	IS_POE3_OEI3		IS11
#define	IS_POE3_OEI4		IS12
#define	IS_RIIC0_TEI0		IS13
#define	IS_RIIC0_EEI0		IS14
#define	IS_RIIC2_TEI2		IS15
#define	IS_RIIC2_EEI2		IS16
#define	IS_SSI0_SSIF0		IS17
#define	IS_SSI1_SSIF1		IS18
#define	IS_S12AD0_S12CMPI0	IS20
#define	IS_S12AD1_S12CMPI1	IS22
#define	IS_SCIFA8_TEIF8		IS0
#define	IS_SCIFA8_ERIF8		IS1
#define	IS_SCIFA8_BRIF8		IS2
#define	IS_SCIFA8_DRIF8		IS3
#define	IS_SCIFA9_TEIF9		IS4
#define	IS_SCIFA9_ERIF9		IS5
#define	IS_SCIFA9_BRIF9		IS6
#define	IS_SCIFA9_DRIF9		IS7
#define	IS_SCIFA10_TEIF10	IS8
#define	IS_SCIFA10_ERIF10	IS9
#define	IS_SCIFA10_BRIF10	IS10
#define	IS_SCIFA10_DRIF10	IS11
#define	IS_SCIFA11_TEIF11	IS12
#define	IS_SCIFA11_ERIF11	IS13
#define	IS_SCIFA11_BRIF11	IS14
#define	IS_SCIFA11_DRIF11	IS15
#define	IS_RSPI0_SPII0		IS16
#define	IS_RSPI0_SPEI0		IS17
#define	IS_RSPI1_SPII1		IS18
#define	IS_RSPI1_SPEI1		IS19
#define	IS_EPTPC_MINT		IS0
#define	IS_PRPEDMAC_PINT	IS1
#define	IS_EDMAC0_EINT0		IS4
#define	IS_EDMAC1_EINT1		IS5

#define	EN_CAN0_ERS0		EN0
#define	EN_CAN1_ERS1		EN1
#define	EN_CAN2_ERS2		EN2
#define	EN_SCI0_TEI0		EN0
#define	EN_SCI0_ERI0		EN1
#define	EN_SCI1_TEI1		EN2
#define	EN_SCI1_ERI1		EN3
#define	EN_SCI2_TEI2		EN4
#define	EN_SCI2_ERI2		EN5
#define	EN_SCI3_TEI3		EN6
#define	EN_SCI3_ERI3		EN7
#define	EN_SCI4_TEI4		EN8
#define	EN_SCI4_ERI4		EN9
#define	EN_SCI5_TEI5		EN10
#define	EN_SCI5_ERI5		EN11
#define	EN_SCI6_TEI6		EN12
#define	EN_SCI6_ERI6		EN13
#define	EN_SCI7_TEI7		EN14
#define	EN_SCI7_ERI7		EN15
#define	EN_SCI12_TEI12		EN16
#define	EN_SCI12_ERI12		EN17
#define	EN_SCI12_SCIX0		EN18
#define	EN_SCI12_SCIX1		EN19
#define	EN_SCI12_SCIX2		EN20
#define	EN_SCI12_SCIX3		EN21
#define	EN_QSPI_QSPSSLI		EN24
#define	EN_CAC_FERRF		EN26
#define	EN_CAC_MENDF		EN27
#define	EN_CAC_OVFF			EN28
#define	EN_DOC_DOPCF		EN29
#define	EN_PDC_PCFEI		EN30
#define	EN_PDC_PCERI		EN31
#define	EN_SRC_PCERI		EN0
#define	EN_SRC_OVF			EN1
#define	EN_SRC_CEF			EN2
#define	EN_SDHI_CDETI		EN3
#define	EN_SDHI_CACI		EN4
#define	EN_SDHI_SDACI		EN5
#define	EN_MMCIF_CDETIO		EN6
#define	EN_MMCIF_ERRIO		EN7
#define	EN_MMCIF_ACCIO		EN8
#define	EN_POE3_OEI1		EN9
#define	EN_POE3_OEI2		EN10
#define	EN_POE3_OEI3		EN11
#define	EN_POE3_OEI4		EN12
#define	EN_RIIC0_TEI0		EN13
#define	EN_RIIC0_EEI0		EN14
#define	EN_RIIC2_TEI2		EN15
#define	EN_RIIC2_EEI2		EN16
#define	EN_SSI0_SSIF0		EN17
#define	EN_SSI1_SSIF1		EN18
#define	EN_S12AD0_S12CMPI0	EN20
#define	EN_S12AD1_S12CMPI1	EN22
#define	EN_SCIFA8_TEIF8		EN0
#define	EN_SCIFA8_ERIF8		EN1
#define	EN_SCIFA8_BRIF8		EN2
#define	EN_SCIFA8_DRIF8		EN3
#define	EN_SCIFA9_TEIF9		EN4
#define	EN_SCIFA9_ERIF9		EN5
#define	EN_SCIFA9_BRIF9		EN6
#define	EN_SCIFA9_DRIF9		EN7
#define	EN_SCIFA10_TEIF10	EN8
#define	EN_SCIFA10_ERIF10	EN9
#define	EN_SCIFA10_BRIF10	EN10
#define	EN_SCIFA10_DRIF10	EN11
#define	EN_SCIFA11_TEIF11	EN12
#define	EN_SCIFA11_ERIF11	EN13
#define	EN_SCIFA11_BRIF11	EN14
#define	EN_SCIFA11_DRIF11	EN15
#define	EN_RSPI0_SPII0		EN16
#define	EN_RSPI0_SPEI0		EN17
#define	EN_RSPI1_SPII1		EN18
#define	EN_RSPI1_SPEI1		EN19
#define	EN_EPTPC_MINT		EN0
#define	EN_PRPEDMAC_PINT	EN1
#define	EN_EDMAC0_EINT0		EN4
#define	EN_EDMAC1_EINT1		EN5

#define	CLR_CAN0_ERS0		CLR0
#define	CLR_CAN1_ERS1		CLR1
#define	CLR_CAN2_ERS2		CLR2
#define	CLR_RSPI1_SPII1		CLR18
#define	CLR_RSPI1_SPEI1		CLR19

#define	GEN_CAN0_ERS0		GENBE0
#define	GEN_CAN1_ERS1		GENBE0
#define	GEN_CAN2_ERS2		GENBE0
#define	GEN_SCI0_TEI0		GENBL0
#define	GEN_SCI0_ERI0		GENBL0
#define	GEN_SCI1_TEI1		GENBL0
#define	GEN_SCI1_ERI1		GENBL0
#define	GEN_SCI2_TEI2		GENBL0
#define	GEN_SCI2_ERI2		GENBL0
#define	GEN_SCI3_TEI3		GENBL0
#define	GEN_SCI3_ERI3		GENBL0
#define	GEN_SCI4_TEI4		GENBL0
#define	GEN_SCI4_ERI4		GENBL0
#define	GEN_SCI5_TEI5		GENBL0
#define	GEN_SCI5_ERI5		GENBL0
#define	GEN_SCI6_TEI6		GENBL0
#define	GEN_SCI6_ERI6		GENBL0
#define	GEN_SCI7_TEI7		GENBL0
#define	GEN_SCI7_ERI7		GENBL0
#define	GEN_SCI12_TEI12		GENBL0
#define	GEN_SCI12_ERI12		GENBL0
#define	GEN_SCI12_SCIX0		GENBL0
#define	GEN_SCI12_SCIX1		GENBL0
#define	GEN_SCI12_SCIX2		GENBL0
#define	GEN_SCI12_SCIX3		GENBL0
#define	GEN_QSPI_QSPSSLI	GENBL0
#define	GEN_CAC_FERRF		GENBL0
#define	GEN_CAC_MENDF		GENBL0
#define	GEN_CAC_OVFF		GENBL0
#define	GEN_DOC_DOPCF		GENBL0
#define	GEN_PDC_PCFEI		GENBL0
#define	GEN_PDC_PCERI		GENBL0
#define	GEN_SRC_PCERI		GENBL1
#define	GEN_SRC_OVF			GENBL1
#define	GEN_SRC_CEF			GENBL1
#define	GEN_SDHI_CDETI		GENBL1
#define	GEN_SDHI_CACI		GENBL1
#define	GEN_SDHI_SDACI		GENBL1
#define	GEN_MMCIF_CDETIO	GENBL1
#define	GEN_MMCIF_ERRIO		GENBL1
#define	GEN_MMCIF_ACCIO		GENBL1
#define	GEN_POE3_OEI1		GENBL1
#define	GEN_POE3_OEI2		GENBL1
#define	GEN_POE3_OEI3		GENBL1
#define	GEN_POE3_OEI4		GENBL1
#define	GEN_RIIC0_TEI0		GENBL1
#define	GEN_RIIC0_EEI0		GENBL1
#define	GEN_RIIC2_TEI2		GENBL1
#define	GEN_RIIC2_EEI2		GENBL1
#define	GEN_SSI0_SSIF0		GENBL1
#define	GEN_SSI1_SSIF1		GENBL1
#define	GEN_S12AD0_S12CMPI0	GENBL1
#define	GEN_S12AD1_S12CMPI1	GENBL1
#define	GEN_SCIFA8_TEIF8	GENAL0
#define	GEN_SCIFA8_ERIF8	GENAL0
#define	GEN_SCIFA8_BRIF8	GENAL0
#define	GEN_SCIFA8_DRIF8	GENAL0
#define	GEN_SCIFA9_TEIF9	GENAL0
#define	GEN_SCIFA9_ERIF9	GENAL0
#define	GEN_SCIFA9_BRIF9	GENAL0
#define	GEN_SCIFA9_DRIF9	GENAL0
#define	GEN_SCIFA10_TEIF10	GENAL0
#define	GEN_SCIFA10_ERIF10	GENAL0
#define	GEN_SCIFA10_BRIF10	GENAL0
#define	GEN_SCIFA10_DRIF10	GENAL0
#define	GEN_SCIFA11_TEIF11	GENAL0
#define	GEN_SCIFA11_ERIF11	GENAL0
#define	GEN_SCIFA11_BRIF11	GENAL0
#define	GEN_SCIFA11_DRIF11	GENAL0
#define	GEN_RSPI0_SPII0		GENAL0
#define	GEN_RSPI0_SPEI0		GENAL0
#define	GEN_RSPI1_SPII1		GENAL0
#define	GEN_RSPI1_SPEI1		GENAL0
#define	GEN_EPTPC_MINT		GENAL1
#define	GEN_PRPEDMAC_PINT	GENAL1
#define	GEN_EDMAC0_EINT0	GENAL1
#define	GEN_EDMAC1_EINT1	GENAL1

#define	GRP_CAN0_ERS0		GRPBE0
#define	GRP_CAN1_ERS1		GRPBE0
#define	GRP_CAN2_ERS2		GRPBE0
#define	GRP_SCI0_TEI0		GRPBL0
#define	GRP_SCI0_ERI0		GRPBL0
#define	GRP_SCI1_TEI1		GRPBL0
#define	GRP_SCI1_ERI1		GRPBL0
#define	GRP_SCI2_TEI2		GRPBL0
#define	GRP_SCI2_ERI2		GRPBL0
#define	GRP_SCI3_TEI3		GRPBL0
#define	GRP_SCI3_ERI3		GRPBL0
#define	GRP_SCI4_TEI4		GRPBL0
#define	GRP_SCI4_ERI4		GRPBL0
#define	GRP_SCI5_TEI5		GRPBL0
#define	GRP_SCI5_ERI5		GRPBL0
#define	GRP_SCI6_TEI6		GRPBL0
#define	GRP_SCI6_ERI6		GRPBL0
#define	GRP_SCI7_TEI7		GRPBL0
#define	GRP_SCI7_ERI7		GRPBL0
#define	GRP_SCI12_TEI12		GRPBL0
#define	GRP_SCI12_ERI12		GRPBL0
#define	GRP_SCI12_SCIX0		GRPBL0
#define	GRP_SCI12_SCIX1		GRPBL0
#define	GRP_SCI12_SCIX2		GRPBL0
#define	GRP_SCI12_SCIX3		GRPBL0
#define	GRP_QSPI_QSPSSLI	GRPBL0
#define	GRP_CAC_FERRF		GRPBL0
#define	GRP_CAC_MENDF		GRPBL0
#define	GRP_CAC_OVFF		GRPBL0
#define	GRP_DOC_DOPCF		GRPBL0
#define	GRP_PDC_PCFEI		GRPBL0
#define	GRP_PDC_PCERI		GRPBL0
#define	GRP_SRC_PCERI		GRPBL1
#define	GRP_SRC_OVF			GRPBL1
#define	GRP_SRC_CEF			GRPBL1
#define	GRP_SDHI_CDETI		GRPBL1
#define	GRP_SDHI_CACI		GRPBL1
#define	GRP_SDHI_SDACI		GRPBL1
#define	GRP_MMCIF_CDETIO	GRPBL1
#define	GRP_MMCIF_ERRIO		GRPBL1
#define	GRP_MMCIF_ACCIO		GRPBL1
#define	GRP_POE3_OEI1		GRPBL1
#define	GRP_POE3_OEI2		GRPBL1
#define	GRP_POE3_OEI3		GRPBL1
#define	GRP_POE3_OEI4		GRPBL1
#define	GRP_RIIC0_TEI0		GRPBL1
#define	GRP_RIIC0_EEI0		GRPBL1
#define	GRP_RIIC2_TEI2		GRPBL1
#define	GRP_RIIC2_EEI2		GRPBL1
#define	GRP_SSI0_SSIF0		GRPBL1
#define	GRP_SSI1_SSIF1		GRPBL1
#define	GRP_S12AD0_S12CMPI0	GRPBL1
#define	GRP_S12AD1_S12CMPI1	GRPBL1
#define	GRP_SCIFA8_TEIF8	GRPAL0
#define	GRP_SCIFA8_ERIF8	GRPAL0
#define	GRP_SCIFA8_BRIF8	GRPAL0
#define	GRP_SCIFA8_DRIF8	GRPAL0
#define	GRP_SCIFA9_TEIF9	GRPAL0
#define	GRP_SCIFA9_ERIF9	GRPAL0
#define	GRP_SCIFA9_BRIF9	GRPAL0
#define	GRP_SCIFA9_DRIF9	GRPAL0
#define	GRP_SCIFA10_TEIF10	GRPAL0
#define	GRP_SCIFA10_ERIF10	GRPAL0
#define	GRP_SCIFA10_BRIF10	GRPAL0
#define	GRP_SCIFA10_DRIF10	GRPAL0
#define	GRP_SCIFA11_TEIF11	GRPAL0
#define	GRP_SCIFA11_ERIF11	GRPAL0
#define	GRP_SCIFA11_BRIF11	GRPAL0
#define	GRP_SCIFA11_DRIF11	GRPAL0
#define	GRP_RSPI0_SPII0		GRPAL0
#define	GRP_RSPI0_SPEI0		GRPAL0
#define	GRP_RSPI1_SPII1		GRPAL0
#define	GRP_RSPI1_SPEI1		GRPAL0
#define	GRP_EPTPC_MINT		GRPAL1
#define	GRP_PRPEDMAC_PINT	GRPAL1
#define	GRP_EDMAC0_EINT0	GRPAL1
#define	GRP_EDMAC1_EINT1	GRPAL1

#define	GCR_CAN0_ERS0		GCRBE0
#define	GCR_CAN1_ERS1		GCRBE0
#define	GCR_CAN2_ERS2		GCRBE0
#define	GCR_RSPI1_SPII1		GCRAL0
#define	GCR_RSPI1_SPEI1		GCRAL0

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

#define	BSC			(*(volatile struct st_bsc      __evenaccess *)0x81300)
#define	CAC			(*(volatile struct st_cac      __evenaccess *)0x8B000)
#define	CAN0		(*(volatile struct st_can      __evenaccess *)0x90200)
#define	CAN1		(*(volatile struct st_can      __evenaccess *)0x91200)
#define	CAN2		(*(volatile struct st_can      __evenaccess *)0x92200)
#define	CMT			(*(volatile struct st_cmt      __evenaccess *)0x88000)
#define	CMT0		(*(volatile struct st_cmt0     __evenaccess *)0x88002)
#define	CMT1		(*(volatile struct st_cmt0     __evenaccess *)0x88008)
#define	CMT2		(*(volatile struct st_cmt0     __evenaccess *)0x88012)
#define	CMT3		(*(volatile struct st_cmt0     __evenaccess *)0x88018)
#define	CMTW0		(*(volatile struct st_cmtw     __evenaccess *)0x94200)
#define	CMTW1		(*(volatile struct st_cmtw     __evenaccess *)0x94280)
#define	CRC			(*(volatile struct st_crc      __evenaccess *)0x88280)
#define	DA			(*(volatile struct st_da       __evenaccess *)0x88040)
#define	DMAC		(*(volatile struct st_dmac     __evenaccess *)0x82200)
#define	DMAC0		(*(volatile struct st_dmac0    __evenaccess *)0x82000)
#define	DMAC1		(*(volatile struct st_dmac1    __evenaccess *)0x82040)
#define	DMAC2		(*(volatile struct st_dmac1    __evenaccess *)0x82080)
#define	DMAC3		(*(volatile struct st_dmac1    __evenaccess *)0x820C0)
#define	DMAC4		(*(volatile struct st_dmac1    __evenaccess *)0x82100)
#define	DMAC5		(*(volatile struct st_dmac1    __evenaccess *)0x82140)
#define	DMAC6		(*(volatile struct st_dmac1    __evenaccess *)0x82180)
#define	DMAC7		(*(volatile struct st_dmac1    __evenaccess *)0x821C0)
#define	DOC			(*(volatile struct st_doc      __evenaccess *)0x8B080)
#define	DTC			(*(volatile struct st_dtc      __evenaccess *)0x82400)
#define	ECCRAM		(*(volatile struct st_eccram   __evenaccess *)0x812C0)
#define	EDMAC0		(*(volatile struct st_edmac    __evenaccess *)0xC0000)
#define	EDMAC1		(*(volatile struct st_edmac    __evenaccess *)0xC0200)
#define	ELC			(*(volatile struct st_elc      __evenaccess *)0x8B100)
#define	EPTPC		(*(volatile struct st_eptpc    __evenaccess *)0xC0500)
#define	EPTPC0		(*(volatile struct st_eptpc0   __evenaccess *)0xC4800)
#define	EPTPC1		(*(volatile struct st_eptpc0   __evenaccess *)0xC4C00)
#define	ETHERC0		(*(volatile struct st_etherc   __evenaccess *)0xC0100)
#define	ETHERC1		(*(volatile struct st_etherc   __evenaccess *)0xC0300)
#define	EXDMAC		(*(volatile struct st_exdmac   __evenaccess *)0x82A00)
#define	EXDMAC0		(*(volatile struct st_exdmac0  __evenaccess *)0x82800)
#define	EXDMAC1		(*(volatile struct st_exdmac1  __evenaccess *)0x82840)
#define	FLASH		(*(volatile struct st_flash    __evenaccess *)0x8C294)
#define	GPT			(*(volatile struct st_gpt      __evenaccess *)0xC2000)
#define	GPT0		(*(volatile struct st_gpt0     __evenaccess *)0xC2100)
#define	GPT1		(*(volatile struct st_gpt0     __evenaccess *)0xC2180)
#define	GPT2		(*(volatile struct st_gpt0     __evenaccess *)0xC2200)
#define	GPT3		(*(volatile struct st_gpt0     __evenaccess *)0xC2280)
#define	ICU			(*(volatile struct st_icu      __evenaccess *)0x87000)
#define	IWDT		(*(volatile struct st_iwdt     __evenaccess *)0x88030)
#define	MMCIF		(*(volatile struct st_mmcif    __evenaccess *)0x88500)
#define	MPC			(*(volatile struct st_mpc      __evenaccess *)0x8C100)
#define	MPU			(*(volatile struct st_mpu      __evenaccess *)0x86400)
#define	MTU			(*(volatile struct st_mtu      __evenaccess *)0xC120A)
#define	MTU0		(*(volatile struct st_mtu0     __evenaccess *)0xC1290)
#define	MTU1		(*(volatile struct st_mtu1     __evenaccess *)0xC1290)
#define	MTU2		(*(volatile struct st_mtu2     __evenaccess *)0xC1292)
#define	MTU3		(*(volatile struct st_mtu3     __evenaccess *)0xC1200)
#define	MTU4		(*(volatile struct st_mtu4     __evenaccess *)0xC1200)
#define	MTU5		(*(volatile struct st_mtu5     __evenaccess *)0xC1A94)
#define	MTU6		(*(volatile struct st_mtu6     __evenaccess *)0xC1A00)
#define	MTU7		(*(volatile struct st_mtu7     __evenaccess *)0xC1A00)
#define	MTU8		(*(volatile struct st_mtu8     __evenaccess *)0xC1298)
#define	PDC			(*(volatile struct st_pdc      __evenaccess *)0xA0500)
#define	POE3		(*(volatile struct st_poe      __evenaccess *)0x8C4C0)
#define	PORT0		(*(volatile struct st_port0    __evenaccess *)0x8C000)
#define	PORT1		(*(volatile struct st_port1    __evenaccess *)0x8C001)
#define	PORT2		(*(volatile struct st_port2    __evenaccess *)0x8C002)
#define	PORT3		(*(volatile struct st_port3    __evenaccess *)0x8C003)
#define	PORT4		(*(volatile struct st_port4    __evenaccess *)0x8C004)
#define	PORT5		(*(volatile struct st_port5    __evenaccess *)0x8C005)
#define	PORT6		(*(volatile struct st_port6    __evenaccess *)0x8C006)
#define	PORT7		(*(volatile struct st_port7    __evenaccess *)0x8C007)
#define	PORT8		(*(volatile struct st_port8    __evenaccess *)0x8C008)
#define	PORT9		(*(volatile struct st_port9    __evenaccess *)0x8C009)
#define	PORTA		(*(volatile struct st_porta    __evenaccess *)0x8C00A)
#define	PORTB		(*(volatile struct st_portb    __evenaccess *)0x8C00B)
#define	PORTC		(*(volatile struct st_portc    __evenaccess *)0x8C00C)
#define	PORTD		(*(volatile struct st_portd    __evenaccess *)0x8C00D)
#define	PORTE		(*(volatile struct st_porte    __evenaccess *)0x8C00E)
#define	PORTF		(*(volatile struct st_portf    __evenaccess *)0x8C00F)
#define	PORTG		(*(volatile struct st_portg    __evenaccess *)0x8C010)
#define	PORTJ		(*(volatile struct st_portj    __evenaccess *)0x8C012)
#define	PPG0		(*(volatile struct st_ppg0     __evenaccess *)0x881E6)
#define	PPG1		(*(volatile struct st_ppg1     __evenaccess *)0x881F0)
#define	PTPEDMAC	(*(volatile struct st_ptpedmac __evenaccess *)0xC0400)
#define	QSPI		(*(volatile struct st_qspi     __evenaccess *)0x89E00)
#define	RAM			(*(volatile struct st_ram      __evenaccess *)0x81200)
#define	RIIC0		(*(volatile struct st_riic     __evenaccess *)0x88300)
#define	RIIC2		(*(volatile struct st_riic     __evenaccess *)0x88340)
#define	RSPI0		(*(volatile struct st_rspi     __evenaccess *)0xD0100)
#define	RSPI1		(*(volatile struct st_rspi     __evenaccess *)0xD0120)
#define	RTC			(*(volatile struct st_rtc      __evenaccess *)0x8C400)
#define	S12AD		(*(volatile struct st_s12ad    __evenaccess *)0x89000)
#define	S12AD1		(*(volatile struct st_s12ad1   __evenaccess *)0x89100)
#define	SCI0		(*(volatile struct st_sci0     __evenaccess *)0x8A000)
#define	SCI1		(*(volatile struct st_sci0     __evenaccess *)0x8A020)
#define	SCI2		(*(volatile struct st_sci0     __evenaccess *)0x8A040)
#define	SCI3		(*(volatile struct st_sci0     __evenaccess *)0x8A060)
#define	SCI4		(*(volatile struct st_sci0     __evenaccess *)0x8A080)
#define	SCI5		(*(volatile struct st_sci0     __evenaccess *)0x8A0A0)
#define	SCI6		(*(volatile struct st_sci0     __evenaccess *)0x8A0C0)
#define	SCI7		(*(volatile struct st_sci0     __evenaccess *)0x8A0E0)
#define	SCI12		(*(volatile struct st_sci12    __evenaccess *)0x8B300)
#define	SCIFA8		(*(volatile struct st_scifa    __evenaccess *)0xD0000)
#define	SCIFA9		(*(volatile struct st_scifa    __evenaccess *)0xD0020)
#define	SCIFA10		(*(volatile struct st_scifa    __evenaccess *)0xD0040)
#define	SCIFA11		(*(volatile struct st_scifa    __evenaccess *)0xD0060)
#define	SDHI		(*(volatile struct st_sdhi     __evenaccess *)0x8AC00)
#define	SMCI0		(*(volatile struct st_smci0    __evenaccess *)0x8A000)
#define	SMCI1		(*(volatile struct st_smci0    __evenaccess *)0x8A020)
#define	SMCI2		(*(volatile struct st_smci0    __evenaccess *)0x8A040)
#define	SMCI3		(*(volatile struct st_smci0    __evenaccess *)0x8A060)
#define	SMCI4		(*(volatile struct st_smci0    __evenaccess *)0x8A080)
#define	SMCI5		(*(volatile struct st_smci0    __evenaccess *)0x8A0A0)
#define	SMCI6		(*(volatile struct st_smci0    __evenaccess *)0x8A0C0)
#define	SMCI7		(*(volatile struct st_smci0    __evenaccess *)0x8A0E0)
#define	SMCI12		(*(volatile struct st_smci0    __evenaccess *)0x8B300)
#define	SRC			(*(volatile struct st_src      __evenaccess *)0x98000)
#define	SSI0		(*(volatile struct st_ssi      __evenaccess *)0x8A500)
#define	SSI1		(*(volatile struct st_ssi      __evenaccess *)0x8A540)
#define	SYSTEM		(*(volatile struct st_system   __evenaccess *)0x80000)
#define	TEMPS		(*(volatile struct st_temps    __evenaccess *)0x8C500)
#define	TMR0		(*(volatile struct st_tmr0     __evenaccess *)0x88200)
#define	TMR1		(*(volatile struct st_tmr1     __evenaccess *)0x88201)
#define	TMR2		(*(volatile struct st_tmr0     __evenaccess *)0x88210)
#define	TMR3		(*(volatile struct st_tmr1     __evenaccess *)0x88211)
#define	TMR01		(*(volatile struct st_tmr01    __evenaccess *)0x88204)
#define	TMR23		(*(volatile struct st_tmr01    __evenaccess *)0x88214)
#define	TPU0		(*(volatile struct st_tpu0     __evenaccess *)0x88108)
#define	TPU1		(*(volatile struct st_tpu1     __evenaccess *)0x88108)
#define	TPU2		(*(volatile struct st_tpu2     __evenaccess *)0x8810A)
#define	TPU3		(*(volatile struct st_tpu3     __evenaccess *)0x8810A)
#define	TPU4		(*(volatile struct st_tpu4     __evenaccess *)0x8810C)
#define	TPU5		(*(volatile struct st_tpu5     __evenaccess *)0x8810C)
#define	TPUA		(*(volatile struct st_tpua     __evenaccess *)0x88100)
#define	USB			(*(volatile struct st_usb      __evenaccess *)0xA0400)
#define	USB0		(*(volatile struct st_usb0     __evenaccess *)0xA0000)
#define	USBA		(*(volatile struct st_usba     __evenaccess *)0xD0400)
#define	WDT			(*(volatile struct st_wdt      __evenaccess *)0x88020)
#pragma bit_order
#pragma packoption
#endif
