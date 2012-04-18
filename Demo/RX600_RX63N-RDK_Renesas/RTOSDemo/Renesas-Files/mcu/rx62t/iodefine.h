/************************************************************************
*
* Device     : RX/RX600/RX62T
*
* File Name  : ioedfine.h
*
* Abstract   : Definition of I/O Register.
*
* History    : 0.20 (2010-05-15) [Hardware Manual Revision : 0.20]
*            : 1.00 (2010-11-03) [Hardware Manual Revision : 1.00]
*            : 1.01 (2011-11-29) Changed IR flag names for FCU flags to 
*                                be the same as other RX devices. 
*                                (IR_FCU_FIFERR=21,IR_FCU_FRDYI=23,)
*                                instead of:
*                                (IR_FCUIF_FIFERR=21,IR_FCUIF_FRDYI=23,)
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
/*  CPU TYPE    : RX62T                                                         */
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
/*       MSTP(SCI0) = 0;    // SCI0,SMCI0                         expands to :  */
/*         SYSTEM.MSTPCRB.BIT.MSTPB31 = 0;                                      */
/*       MSTP(MTU4) = 0;    // MTU,MTU0,MTU1,MTU2,MTU3,MTU4,...   expands to :  */
/*         SYSTEM.MSTPCRA.BIT.MSTPA9  = 0;                                      */
/*       MSTP(CMT3) = 0;    // CMT2,CMT3                          expands to :  */
/*         SYSTEM.MSTPCRA.BIT.MSTPA14 = 0;                                      */
/*                                                                              */
/*                                                                              */
/********************************************************************************/
#ifndef __RX62TIODEFINE_HEADER__
#define __RX62TIODEFINE_HEADER__
#pragma bit_order left
#pragma unpack
struct st_ad {
	unsigned short ADDRA;
	unsigned short ADDRB;
	unsigned short ADDRC;
	unsigned short ADDRD;
	unsigned short ADDRE;
	unsigned short ADDRF;
	unsigned short ADDRG;
	unsigned short ADDRH;
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
			unsigned char :4;
			unsigned char CKS:2;
			unsigned char MODE:2;
		} BIT;
	} ADCR;
	char           wk0[9];
	unsigned char  ADSSTR;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char DIAG:2;
		} BIT;
	} ADDIAGR;
	char           wk2[2];
	unsigned short ADDRI;
	unsigned short ADDRJ;
	unsigned short ADDRK;
	unsigned short ADDRL;
	char           wk3[8];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char ADSTRS:5;
		} BIT;
	} ADSTRGR;
	char           wk4[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char DPSEL:1;
			unsigned char :6;
			unsigned char DPPRC:1;
		} BIT;
	} ADDPR;
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
			unsigned char :7;
			unsigned char IGAEN:1;
		} BIT;
	} BEREN;
	char           wk1[3];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char MST:3;
			unsigned char :3;
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
			unsigned short DBRE7:1;
			unsigned short DBRE6:1;
			unsigned short DBRE5:1;
			unsigned short DBRE4:1;
			unsigned short DBRE3:1;
			unsigned short DBRE2:1;
			unsigned short DBRE1:1;
			unsigned short DBRE0:1;
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
			unsigned short DBRE9:1;
			unsigned short DBRE8:1;
		} BIT;
	} DFLRE1;
	char           wk4[12];
	union {
		unsigned short WORD;
		struct {
			unsigned short KEY:8;
			unsigned short DBWE7:1;
			unsigned short DBWE6:1;
			unsigned short DBWE5:1;
			unsigned short DBWE4:1;
			unsigned short DBWE3:1;
			unsigned short DBWE2:1;
			unsigned short DBWE1:1;
			unsigned short DBWE0:1;
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
			unsigned short DBWE9:1;
			unsigned short DBWE8:1;
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
			unsigned short FRKEY:8;
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

struct st_gpt {
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char :8;
			unsigned char :4;
			unsigned char CST3:1;
			unsigned char CST2:1;
			unsigned char CST1:1;
			unsigned char CST0:1;
		} BIT;
	} GTSTR;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char CPHW3:2;
			unsigned char CPHW2:2;
			unsigned char CPHW1:2;
			unsigned char CPHW0:2;
			unsigned char CSHW3:2;
			unsigned char CSHW2:2;
			unsigned char CSHW1:2;
			unsigned char CSHW0:2;
		} BIT;
	} GTHSCR;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char :4;
			unsigned char CCSW3:1;
			unsigned char CCSW2:1;
			unsigned char CCSW1:1;
			unsigned char CCSW0:1;
			unsigned char CCHW3:2;
			unsigned char CCHW2:2;
			unsigned char CCHW1:2;
			unsigned char CCHW0:2;
		} BIT;
	} GTHCCR;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char CSHSL3:4;
			unsigned char CSHSL2:4;
			unsigned char CSHSL1:4;
			unsigned char CSHSL0:4;
		} BIT;
	} GTHSSR;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char CSHPL3:4;
			unsigned char CSHPL2:4;
			unsigned char CSHPL1:4;
			unsigned char CSHPL0:4;
		} BIT;
	} GTHPSR;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char :8;
			unsigned char :4;
			unsigned char WP3:1;
			unsigned char WP2:1;
			unsigned char WP1:1;
			unsigned char WP0:1;
		} BIT;
	} GTWP;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char :2;
			unsigned char SYNC3:2;
			unsigned char :2;
			unsigned char SYNC2:2;
			unsigned char :2;
			unsigned char SYNC1:2;
			unsigned char :2;
			unsigned char SYNC0:2;
		} BIT;
	} GTSYNC;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char :6;
			unsigned char ETINF:1;
			unsigned char ETIPF:1;
			unsigned char :6;
			unsigned char ETINEN:1;
			unsigned char ETIPEN:1;
		} BIT;
	} GTETINT;
	char           wk1[2];
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char BD33:1;
			unsigned char BD32:1;
			unsigned char BD31:1;
			unsigned char BD30:1;
			unsigned char BD23:1;
			unsigned char BD22:1;
			unsigned char BD21:1;
			unsigned char BD20:1;
			unsigned char BD13:1;
			unsigned char BD12:1;
			unsigned char BD11:1;
			unsigned char BD10:1;
			unsigned char BD03:1;
			unsigned char BD02:1;
			unsigned char BD01:1;
			unsigned char BD00:1;
		} BIT;
	} GTBDR;
	char           wk2[106];
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char LPSC:2;
			unsigned char TPSC:2;
			unsigned char LCNTAT:1;
			unsigned char LCTO:3;
			unsigned char :1;
			unsigned char LCINTO:1;
			unsigned char LCINTD:1;
			unsigned char LCINTC:1;
			unsigned char :1;
			unsigned char LCNTS:1;
			unsigned char LCNTCR:1;
			unsigned char LCNTE:1;
		} BIT;
	} LCCR;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char :8;
			unsigned char :5;
			unsigned char LISO:1;
			unsigned char LISD:1;
			unsigned char LISC:1;
		} BIT;
	} LCST;
	unsigned short LCNT;
	unsigned short LCNTA;
	unsigned short LCNT00;
	unsigned short LCNT01;
	unsigned short LCNT02;
	unsigned short LCNT03;
	unsigned short LCNT04;
	unsigned short LCNT05;
	unsigned short LCNT06;
	unsigned short LCNT07;
	unsigned short LCNT08;
	unsigned short LCNT09;
	unsigned short LCNT10;
	unsigned short LCNT11;
	unsigned short LCNT12;
	unsigned short LCNT13;
	unsigned short LCNT14;
	unsigned short LCNT15;
	unsigned short LCNTDU;
	unsigned short LCNTDL;
};

struct st_gpt0 {
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char OBHLD:1;
			unsigned char OBDFLT:1;
			unsigned char GTIOB:6;
			unsigned char OAHLD:1;
			unsigned char OADFLT:1;
			unsigned char GTIOA:6;
		} BIT;
	} GTIOR;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char ADTRBDEN:1;
			unsigned char ADTRBUEN:1;
			unsigned char ADTRADEN:1;
			unsigned char ADTRAUEN:1;
			unsigned char EINT:1;
			unsigned char :3;
			unsigned char GTINTPR:2;
			unsigned char GTINTF:1;
			unsigned char GTINTE:1;
			unsigned char GTINTD:1;
			unsigned char GTINTC:1;
			unsigned char GTINTB:1;
			unsigned char GTINTA:1;
		} BIT;
	} GTINTAD;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char :2;
			unsigned char CCLR:2;
			unsigned char :2;
			unsigned char TPCS:2;
			unsigned char :5;
			unsigned char MD:3;
		} BIT;
	} GTCR;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char :1;
			unsigned char ADTDB:1;
			unsigned char ADTTB:2;
			unsigned char :1;
			unsigned char ADTDA:1;
			unsigned char ADTTA:2;
			unsigned char :1;
			unsigned char CCRSWT:1;
			unsigned char PR:2;
			unsigned char CCRB:2;
			unsigned char CCRA:2;
		} BIT;
	} GTBER;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char :8;
			unsigned char :6;
			unsigned char UDF:1;
			unsigned char UD:1;
		} BIT;
	} GTUDC;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char :1;
			unsigned char ADTBL:1;
			unsigned char :1;
			unsigned char ADTAL:1;
			unsigned char :1;
			unsigned char IVTT:3;
			unsigned char IVTC:2;
			unsigned char ITLF:1;
			unsigned char ITLE:1;
			unsigned char ITLD:1;
			unsigned char ITLC:1;
			unsigned char ITLB:1;
			unsigned char ITLA:1;
		} BIT;
	} GTITC;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char TUCF:1;
			unsigned char :3;
			unsigned char DTEF:1;
			unsigned char ITCNT:3;
			unsigned char TCFPU:1;
			unsigned char TCFPO:1;
			unsigned char TCFF:1;
			unsigned char TCFE:1;
			unsigned char TCFD:1;
			unsigned char TCFC:1;
			unsigned char TCFB:1;
			unsigned char TCFA:1;
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
	} IPR[145];
	char           wk5[367];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char IRQMD:2;
		} BIT;
	} IRQCR[8];
	char           wk6[120];
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
			unsigned char :4;
			unsigned char ITS1:2;
			unsigned char ITS0:2;
		} BIT;
	} PF8IRQ;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char ITS2:1;
		} BIT;
	} PF9IRQ;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char ADTRG1S:1;
			unsigned char ADTRG0S:1;
		} BIT;
	} PFAADC;
	char           wk0[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char TCLKS:2;
			unsigned char :4;
			unsigned char MTUS1:1;
			unsigned char MTUS0:1;
		} BIT;
	} PFCMTU;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char GPTS:1;
		} BIT;
	} PFDGPT;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char SCI2S:1;
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
		} BIT;
	} PFGSPI;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char RSPIS:2;
		} BIT;
	} PFHSPI;
	char           wk2[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char CANS:2;
			unsigned char :5;
			unsigned char CANE:1;
		} BIT;
	} PFJCAN;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char LINE:1;
		} BIT;
	} PFKLIN;
	char           wk3[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :3;
			unsigned char POE11E:1;
			unsigned char POE10E:1;
			unsigned char POE8E:1;
			unsigned char POE4E:1;
			unsigned char POE0E:1;
		} BIT;
	} PFMPOE;
	union {
		unsigned char BYTE;
		struct {
			unsigned char POE10S:1;
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

struct st_lin {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char LWBR0:1;
		} BIT;
	} LWBR;
	unsigned char  LBRP0;
	unsigned char  LBRP1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char LSTM:1;
		} BIT;
	} LSTC;
	char           wk0[3];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char LCKS:2;
		} BIT;
	} LMD;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char BDT:2;
			unsigned char BLT:4;
		} BIT;
	} LBRK;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char IBS:2;
			unsigned char :1;
			unsigned char IBSH:3;
		} BIT;
	} LSPC;
	union {
		unsigned char BYTE;
		struct {
			unsigned char WUTL:4;
		} BIT;
	} LWUP;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char ERRIE:1;
			unsigned char FRCIE:1;
			unsigned char FTCIE:1;
		} BIT;
	} LIE;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
			unsigned char FERE:1;
			unsigned char FTERE:1;
			unsigned char PBERE:1;
			unsigned char BERE:1;
		} BIT;
	} LEDE;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char OM1:1;
			unsigned char OM0:1;
		} BIT;
	} LC;
	char           wk1[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char RTS:1;
			unsigned char FTS:1;
		} BIT;
	} LTC;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char OMM1:1;
			unsigned char OMM0:1;
		} BIT;
	} LMST;
	union {
		unsigned char BYTE;
		struct {
			unsigned char HTRC:1;
			unsigned char D1RC:1;
			unsigned char :2;
			unsigned char ERR:1;
			unsigned char :1;
			unsigned char FRC:1;
			unsigned char FTC:1;
		} BIT;
	} LST;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char CSER:1;
			unsigned char :1;
			unsigned char FER:1;
			unsigned char FTER:1;
			unsigned char PBER:1;
			unsigned char BER:1;
		} BIT;
	} LEST;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :1;
			unsigned char FSM:1;
			unsigned char CSM:1;
			unsigned char RFT:1;
			unsigned char RFDL:4;
		} BIT;
	} LRFC;
	union {
		unsigned char BYTE;
		struct {
			unsigned char IDP:1;
			unsigned char :1;
			unsigned char ID:1;
		} BIT;
	} LIDB;
	unsigned char  LCBR;
	char           wk2[1];
	unsigned char  LDB1;
	unsigned char  LDB2;
	unsigned char  LDB3;
	unsigned char  LDB4;
	unsigned char  LDB5;
	unsigned char  LDB6;
	unsigned char  LDB7;
	unsigned char  LDB8;
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
			unsigned char :6;
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
			unsigned char :3;
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
	char           wk12[2];
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
	} TGCRB;
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
	char           wk19[19];
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
	char           wk20[15];
	union {
		unsigned char BYTE;
		struct {
			unsigned char CCE:1;
			unsigned char :6;
			unsigned char WRE:1;
		} BIT;
	} TWCRB;
	char           wk21[15];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :7;
			unsigned char DRS:1;
		} BIT;
	} TMDR2B;
	char           wk22[15];
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
	char           wk23[2];
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
	char           wk0[16];
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
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char TGFF:1;
			unsigned char TGFE:1;
		} BIT;
	} TSR2;
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
			unsigned char :2;
			unsigned char TCFV:1;
			unsigned char TGFD:1;
			unsigned char TGFC:1;
			unsigned char TGFB:1;
			unsigned char TGFA:1;
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
	char           wk8[57];
	unsigned short TGRE;
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
			unsigned char :2;
			unsigned char TCFV:1;
			unsigned char TGFD:1;
			unsigned char TGFC:1;
			unsigned char TGFB:1;
			unsigned char TGFA:1;
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
	char           wk11[40];
	unsigned short TGRE;
	unsigned short TGRF;
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
	char           wk5[9];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char CMFU5:1;
			unsigned char CMFV5:1;
			unsigned char CMFW5:1;
		} BIT;
	} TSR;
	char           wk6[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char TGIE5U:1;
			unsigned char TGIE5V:1;
			unsigned char TGIE5W:1;
		} BIT;
	} TIER;
	char           wk7[1];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char CSTU5:1;
			unsigned char CSTV5:1;
			unsigned char CSTW5:1;
		} BIT;
	} TSTR;
	char           wk8[1];
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

struct st_poe {
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char :3;
			unsigned char POE0F:1;
			unsigned char :3;
			unsigned char PIE1:1;
			unsigned char :6;
			unsigned char POE0M:2;
		} BIT;
	} ICSR1;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char OSF1:1;
			unsigned char :5;
			unsigned char OCE1:1;
			unsigned char OIE1:1;
		} BIT;
	} OCSR1;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char :3;
			unsigned char POE4F:1;
			unsigned char :3;
			unsigned char PIE2:1;
			unsigned char :6;
			unsigned char POE4M:2;
		} BIT;
	} ICSR2;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char OSF2:1;
			unsigned char :5;
			unsigned char OCE2:1;
			unsigned char OIE2:1;
		} BIT;
	} OCSR2;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char :3;
			unsigned char POE8F:1;
			unsigned char :2;
			unsigned char POE8E:1;
			unsigned char PIE3:1;
			unsigned char :6;
			unsigned char POE8M:2;
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
			unsigned short CMADDMT67ZE:1;
			unsigned short :2;
			unsigned short IC5ADDMT34ZE:1;
			unsigned short IC4ADDMT34ZE:1;
			unsigned short IC3ADDMT34ZE:1;
			unsigned short IC2ADDMT34ZE:1;
			unsigned short :1;
			unsigned short CMADDMT34ZE:1;
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
			unsigned short CMADDMT0ZE:1;
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
			unsigned short CMADDGPT23ZE:1;
			unsigned short :2;
			unsigned short IC5ADDGPT01ZE:1;
			unsigned short :1;
			unsigned short IC3ADDGPT01ZE:1;
			unsigned short IC2ADDGPT01ZE:1;
			unsigned short IC1ADDGPT01ZE:1;
			unsigned short CMADDGPT01ZE:1;
		} BIT;
	} POECR6;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char :3;
			unsigned char POE10F:1;
			unsigned char :2;
			unsigned char POE10E:1;
			unsigned char PIE4:1;
			unsigned char :6;
			unsigned char POE10M:2;
		} BIT;
	} ICSR4;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char :3;
			unsigned char POE11F:1;
			unsigned char :2;
			unsigned char POE11E:1;
			unsigned char PIE5:1;
			unsigned char :6;
			unsigned char POE11M:2;
		} BIT;
	} ICSR5;
	union {
		unsigned short WORD;
		struct {
			unsigned char H;
			unsigned char L;
		} BYTE;
		struct {
			unsigned char :8;
			unsigned char OLSEN:1;
			unsigned char :1;
			unsigned char OLSG2B:1;
			unsigned char OLSG2A:1;
			unsigned char OLSG1B:1;
			unsigned char OLSG1A:1;
			unsigned char OLSG0B:1;
			unsigned char OLSG0A:1;
		} BIT;
	} ALR1;
};

struct st_port1 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PORT;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :6;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ICR;
};

struct st_port2 {
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

struct st_port3 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :4;
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
			unsigned char :4;
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
			unsigned char :4;
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
			unsigned char :4;
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
	} PORT;
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
	} ICR;
};

struct st_port5 {
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
	} ICR;
};

struct st_port6 {
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
	} ICR;
};

struct st_port7 {
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

struct st_port8 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DDR;
	char           wk0[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} DR;
	char           wk1[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
			unsigned char B2:1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} PORT;
	char           wk2[31];
	union {
		unsigned char BYTE;
		struct {
			unsigned char :5;
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

struct st_porta {
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
};

struct st_porte {
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char B5:1;
			unsigned char B4:1;
			unsigned char B3:1;
			unsigned char :1;
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
			unsigned char :1;
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
			unsigned char :1;
			unsigned char B1:1;
			unsigned char B0:1;
		} BIT;
	} ICR;
};

struct st_portg {
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
			unsigned char :1;
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
	unsigned char  SPBR;
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

struct st_s12ad {
	union {
		unsigned short WORD;
		struct {
			unsigned short :2;
			unsigned short CEN102:2;
			unsigned short CEN101:2;
			unsigned short CEN100:2;
			unsigned short :2;
			unsigned short CEN002:2;
			unsigned short CEN001:2;
			unsigned short CEN000:2;
		} BIT;
	} ADCMPMD0;
	union {
		unsigned short WORD;
		struct {
			unsigned short :1;
			unsigned short VSELL1:1;
			unsigned short VSELH1:1;
			unsigned short CSEL1:1;
			unsigned short :1;
			unsigned short VSELL0:1;
			unsigned short VSELH0:1;
			unsigned short CSEL0:1;
			unsigned short :1;
			unsigned short REFH:3;
			unsigned short :1;
			unsigned short REFL:3;
		} BIT;
	} ADCMPMD1;
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short C002NR:4;
			unsigned short C001NR:4;
			unsigned short C000NR:4;
		} BIT;
	} ADCMPNR0;
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short C102NR:4;
			unsigned short C101NR:4;
			unsigned short C100NR:4;
		} BIT;
	} ADCMPNR1;
	union {
		unsigned char BYTE;
		struct {
			unsigned char :2;
			unsigned char C102FLAG:1;
			unsigned char C101FLAG:1;
			unsigned char C100FLAG:1;
			unsigned char C002FLAG:1;
			unsigned char C001FLAG:1;
			unsigned char C000FLAG:1;
		} BIT;
	} ADCMPFR;
	char           wk0[1];
	union {
		unsigned short WORD;
		struct {
			unsigned short :6;
			unsigned short POERQ:1;
			unsigned short IE:1;
			unsigned short :2;
			unsigned short SEL102:1;
			unsigned short SEL101:1;
			unsigned short SEL100:1;
			unsigned short SEL002:1;
			unsigned short SEL001:1;
			unsigned short SEL000:1;
		} BIT;
	} ADCMPSEL;
};

struct st_s12ad0 {
	union {
		unsigned char BYTE;
		struct {
			unsigned char ADST:1;
			unsigned char ADCS:2;
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
			unsigned short :2;
			unsigned short CH:2;
			unsigned short :1;
			unsigned short PG002SEL:1;
			unsigned short PG001SEL:1;
			unsigned short PG000SEL:1;
			unsigned short :5;
			unsigned short PG002EN:1;
			unsigned short PG001EN:1;
			unsigned short PG000EN:1;
		} BIT;
	} ADANS;
	char           wk1[4];
	union {
		unsigned short WORD;
		struct {
			unsigned short :4;
			unsigned short PG002GAIN:4;
			unsigned short PG001GAIN:4;
			unsigned short PG000GAIN:4;
		} BIT;
	} ADPG;
	char           wk2[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short ADRFMT:1;
			unsigned short :1;
			unsigned short ADIEW:1;
			unsigned short ADIE2:1;
			unsigned short DIAGM:1;
			unsigned short DIAGLD:1;
			unsigned short DIAGVAL:2;
			unsigned short :2;
			unsigned short ACE:1;
			unsigned short :2;
			unsigned short ADPRC:2;
			unsigned short SHBYP:1;
		} BIT;
	} ADCER;
	union {
		unsigned short WORD;
		struct {
			unsigned short :3;
			unsigned short ADSTRS1:5;
			unsigned short :3;
			unsigned short ADSTRS0:5;
		} BIT;
	} ADSTRGR;
	char           wk3[12];
	union {
		unsigned short WORD;
		union {
			struct {
				unsigned short DIAGST:2;
				unsigned short :2;
				unsigned short DATA:12;
			} RIGHT;
			struct {
				unsigned short DATA:12;
				unsigned short :2;
				unsigned short DIAGST:2;
			} LEFT;
		} BIT;
	} ADRD;
	unsigned short ADDR0A;
	unsigned short ADDR1;
	unsigned short ADDR2;
	unsigned short ADDR3;
	char           wk4[8];
	unsigned short ADDR0B;
	char           wk5[46];
	unsigned char  ADSSTR;
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
			unsigned char :2;
			unsigned char NFEN:1;
			unsigned char ABCS:1;
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
			unsigned short :11;
			unsigned short BOTS:1;
			unsigned short :3;
			unsigned short IROM:1;
		} BIT;
	} MDSR;
	char           wk0[2];
	union {
		unsigned short WORD;
		struct {
			unsigned short KEY:8;
			unsigned short :7;
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
			unsigned short :2;
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
			unsigned long :3;
			unsigned long MSTPA24:1;
			unsigned long MSTPA23:1;
			unsigned long :5;
			unsigned long MSTPA17:1;
			unsigned long MSTPA16:1;
			unsigned long MSTPA15:1;
			unsigned long MSTPA14:1;
			unsigned long :4;
			unsigned long MSTPA9:1;
			unsigned long :1;
			unsigned long MSTPA7:1;
		} BIT;
	} MSTPCRA;
	union {
		unsigned long LONG;
		struct {
			unsigned long MSTPB31:1;
			unsigned long MSTPB30:1;
			unsigned long MSTPB29:1;
			unsigned long :5;
			unsigned long MSTPB23:1;
			unsigned long :1;
			unsigned long MSTPB21:1;
			unsigned long :3;
			unsigned long MSTPB17:1;
			unsigned long :9;
			unsigned long MSTPB7:1;
			unsigned long :6;
			unsigned long MSTPB0:1;
		} BIT;
	} MSTPCRB;
	union {
		unsigned long LONG;
		struct {
			unsigned long :31;
			unsigned long MSTPC0:1;
		} BIT;
	} MSTPCRC;
	char           wk3[4];
	union {
		unsigned long LONG;
		struct {
			unsigned long :4;
			unsigned long ICK:4;
			unsigned long :12;
			unsigned long PCK:4;
		} BIT;
	} SCKCR;
	char           wk4[28];
	union {
		unsigned short WORD;
		struct {
			unsigned short KEY:8;
			unsigned short OSTDE:1;
			unsigned short OSTDF:1;
		} BIT;
	} OSTDCR;
	char           wk5[49726];
	union {
		unsigned char BYTE;
		struct {
			unsigned char DPSBY:1;
			unsigned char IOKEEP:1;
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
			unsigned char :2;
			unsigned char DLVDE:1;
			unsigned char :2;
			unsigned char DIRQ1E:1;
			unsigned char DIRQ0E:1;
		} BIT;
	} DPSIER;
	union {
		unsigned char BYTE;
		struct {
			unsigned char DNMIF:1;
			unsigned char :2;
			unsigned char DLVDF:1;
			unsigned char :2;
			unsigned char DIRQ1F:1;
			unsigned char DIRQ0F:1;
		} BIT;
	} DPSIFR;
	union {
		unsigned char BYTE;
		struct {
			unsigned char DNMIEG:1;
			unsigned char :5;
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
	char           wk6[6];
	union {
		unsigned char BYTE;
		struct {
			unsigned char KEY:8;
		} BIT;
	} LVDKEYR;
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
	char           wk7[2];
	unsigned char  DPSBKR[32];
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
IR_RSPI0_SPEI0=44,IR_RSPI0_SPRI0,IR_RSPI0_SPTI0,IR_RSPI0_SPII0,
IR_CAN0_ERS0=56,IR_CAN0_RXF0,IR_CAN0_TXF0,IR_CAN0_RXM0,IR_CAN0_TXM0,
IR_ICU_IRQ0=64,IR_ICU_IRQ1,IR_ICU_IRQ2,IR_ICU_IRQ3,IR_ICU_IRQ4,IR_ICU_IRQ5,IR_ICU_IRQ6,IR_ICU_IRQ7,
IR_WDT_WOVI=96,
IR_AD0_ADI0=98,
IR_S12AD0_S12ADI0=102,
IR_S12AD1_S12ADI1,
IR_S12AD_CMPI=106,
IR_MTU0_TGIA0=114,IR_MTU0_TGIB0,IR_MTU0_TGIC0,IR_MTU0_TGID0,IR_MTU0_TCIV0,IR_MTU0_TGIE0,IR_MTU0_TGIF0,
IR_MTU1_TGIA1,IR_MTU1_TGIB1,IR_MTU1_TCIV1,IR_MTU1_TCIU1,
IR_MTU2_TGIA2,IR_MTU2_TGIB2,IR_MTU2_TCIV2,IR_MTU2_TCIU2,
IR_MTU3_TGIA3,IR_MTU3_TGIB3,IR_MTU3_TGIC3,IR_MTU3_TGID3,IR_MTU3_TCIV3,
IR_MTU4_TGIA4,IR_MTU4_TGIB4,IR_MTU4_TGIC4,IR_MTU4_TGID4,IR_MTU4_TCIV4,
IR_MTU5_TGIU5,IR_MTU5_TGIV5,IR_MTU5_TGIW5,
IR_MTU6_TGIA6,IR_MTU6_TGIB6,IR_MTU6_TGIC6,IR_MTU6_TGID6,IR_MTU6_TCIV6,
IR_MTU7_TGIA7=149,IR_MTU7_TGIB7,IR_MTU7_TGIC7,IR_MTU7_TGID7,IR_MTU7_TCIV7,
IR_POE_OEI1=170,IR_POE_OEI2,IR_POE_OEI3,IR_POE_OEI4,
IR_GPT0_GTCIA0,IR_GPT0_GTCIB0,IR_GPT0_GTCIC0,IR_GPT0_GTCIE0,IR_GPT0_GTCIV0,IR_GPT0_LOCO1,
IR_GPT1_GTCIA1,IR_GPT1_GTCIB1,IR_GPT1_GTCIC1,IR_GPT1_GTCIE1,IR_GPT1_GTCIV1,
IR_GPT2_GTCIA2=186,IR_GPT2_GTCIB2,IR_GPT2_GTCIC2,IR_GPT2_GTCIE2,IR_GPT2_GTCIV2,
IR_GPT3_GTCIA3=192,IR_GPT3_GTCIB3,IR_GPT3_GTCIC3,IR_GPT3_GTCIE3,IR_GPT3_GTCIV3,
IR_SCI0_ERI0=214,IR_SCI0_RXI0,IR_SCI0_TXI0,IR_SCI0_TEI0,
IR_SCI1_ERI1,IR_SCI1_RXI1,IR_SCI1_TXI1,IR_SCI1_TEI1,
IR_SCI2_ERI2,IR_SCI2_RXI2,IR_SCI2_TXI2,IR_SCI2_TEI2,
IR_RIIC0_ICEEI0=246,IR_RIIC0_ICRXI0,IR_RIIC0_ICTXI0,IR_RIIC0_ICTEI0,
IR_LIN0_LIN0=254
};

enum enum_dtce {
DTCE_ICU_SWINT=27,
DTCE_CMT0_CMI0,
DTCE_CMT1_CMI1,
DTCE_CMT2_CMI2,
DTCE_CMT3_CMI3,
DTCE_RSPI0_SPRI0=45,DTCE_RSPI0_SPTI0,
DTCE_ICU_IRQ0=64,DTCE_ICU_IRQ1,DTCE_ICU_IRQ2,DTCE_ICU_IRQ3,DTCE_ICU_IRQ4,DTCE_ICU_IRQ5,DTCE_ICU_IRQ6,DTCE_ICU_IRQ7,
DTCE_AD0_ADI0=98,
DTCE_S12AD0_S12ADI0=102,
DTCE_S12AD1_S12ADI1,
DTCE_S12AD_CMPI=106,
DTCE_MTU0_TGIA0=114,DTCE_MTU0_TGIB0,DTCE_MTU0_TGIC0,DTCE_MTU0_TGID0,
DTCE_MTU1_TGIA1=121,DTCE_MTU1_TGIB1,
DTCE_MTU2_TGIA2=125,DTCE_MTU2_TGIB2,
DTCE_MTU3_TGIA3=129,DTCE_MTU3_TGIB3,DTCE_MTU3_TGIC3,DTCE_MTU3_TGID3,
DTCE_MTU4_TGIA4=134,DTCE_MTU4_TGIB4,DTCE_MTU4_TGIC4,DTCE_MTU4_TGID4,DTCE_MTU4_TCIV4,
DTCE_MTU5_TGIU5,DTCE_MTU5_TGIV5,DTCE_MTU5_TGIW5,
DTCE_MTU6_TGIA6,DTCE_MTU6_TGIB6,DTCE_MTU6_TGIC6,DTCE_MTU6_TGID6,
DTCE_MTU7_TGIA7=149,DTCE_MTU7_TGIB7,DTCE_MTU7_TGIC7,DTCE_MTU7_TGID7,DTCE_MTU7_TCIV7,
DTCE_GPT0_GTCIA0=174,DTCE_GPT0_GTCIB0,DTCE_GPT0_GTCIC0,DTCE_GPT0_GTCIE0,DTCE_GPT0_GTCIV0,DTCE_GPT0_LOCO1,
DTCE_GPT1_GTCIA1,DTCE_GPT1_GTCIB1,DTCE_GPT1_GTCIC1,DTCE_GPT1_GTCIE1,DTCE_GPT1_GTCIV1,
DTCE_GPT2_GTCIA2=186,DTCE_GPT2_GTCIB2,DTCE_GPT2_GTCIC2,DTCE_GPT2_GTCIE2,DTCE_GPT2_GTCIV2,
DTCE_GPT3_GTCIA3=192,DTCE_GPT3_GTCIB3,DTCE_GPT3_GTCIC3,DTCE_GPT3_GTCIE3,DTCE_GPT3_GTCIV3,
DTCE_SCI0_RXI0=215,DTCE_SCI0_TXI0,
DTCE_SCI1_RXI1=219,DTCE_SCI1_TXI1,
DTCE_SCI2_RXI2=223,DTCE_SCI2_TXI2,
DTCE_RIIC0_ICRXI0=247,DTCE_RIIC0_ICTXI0,
DTCE_LIN0_LIN0=254
};

enum enum_ier {
IER_BSC_BUSERR=0x02,
IER_FCU_FIFERR=0x02,IER_FCU_FRDYI=0x02,
IER_ICU_SWINT=0x03,
IER_CMT0_CMI0=0x03,
IER_CMT1_CMI1=0x03,
IER_CMT2_CMI2=0x03,
IER_CMT3_CMI3=0x03,
IER_RSPI0_SPEI0=0x05,IER_RSPI0_SPRI0=0x05,IER_RSPI0_SPTI0=0x05,IER_RSPI0_SPII0=0x05,
IER_CAN0_ERS0=0x07,IER_CAN0_RXF0=0x07,IER_CAN0_TXF0=0x07,IER_CAN0_RXM0=0x07,IER_CAN0_TXM0=0x07,
IER_ICU_IRQ0=0x08,IER_ICU_IRQ1=0x08,IER_ICU_IRQ2=0x08,IER_ICU_IRQ3=0x08,IER_ICU_IRQ4=0x08,IER_ICU_IRQ5=0x08,IER_ICU_IRQ6=0x08,IER_ICU_IRQ7=0x08,
IER_WDT_WOVI=0x0C,
IER_AD0_ADI0=0x0C,
IER_S12AD0_S12ADI0=0x0C,
IER_S12AD1_S12ADI1=0x0C,
IER_S12AD_CMPI=0x0D,
IER_MTU0_TGIA0=0x0E,IER_MTU0_TGIB0=0x0E,IER_MTU0_TGIC0=0x0E,IER_MTU0_TGID0=0x0E,IER_MTU0_TCIV0=0x0E,IER_MTU0_TGIE0=0x0E,IER_MTU0_TGIF0=0x0F,
IER_MTU1_TGIA1=0x0F,IER_MTU1_TGIB1=0x0F,IER_MTU1_TCIV1=0x0F,IER_MTU1_TCIU1=0x0F,
IER_MTU2_TGIA2=0x0F,IER_MTU2_TGIB2=0x0F,IER_MTU2_TCIV2=0x0F,IER_MTU2_TCIU2=0x10,
IER_MTU3_TGIA3=0x10,IER_MTU3_TGIB3=0x10,IER_MTU3_TGIC3=0x10,IER_MTU3_TGID3=0x10,IER_MTU3_TCIV3=0x10,
IER_MTU4_TGIA4=0x10,IER_MTU4_TGIB4=0x10,IER_MTU4_TGIC4=0x11,IER_MTU4_TGID4=0x11,IER_MTU4_TCIV4=0x11,
IER_MTU5_TGIU5=0x11,IER_MTU5_TGIV5=0x11,IER_MTU5_TGIW5=0x11,
IER_MTU6_TGIA6=0x11,IER_MTU6_TGIB6=0x11,IER_MTU6_TGIC6=0x12,IER_MTU6_TGID6=0x12,IER_MTU6_TCIV6=0x12,
IER_MTU7_TGIA7=0x12,IER_MTU7_TGIB7=0x12,IER_MTU7_TGIC7=0x12,IER_MTU7_TGID7=0x13,IER_MTU7_TCIV7=0x13,
IER_POE_OEI1=0x15,IER_POE_OEI2=0x15,IER_POE_OEI3=0x15,IER_POE_OEI4=0x15,
IER_GPT0_GTCIA0=0x15,IER_GPT0_GTCIB0=0x15,IER_GPT0_GTCIC0=0x16,IER_GPT0_GTCIE0=0x16,IER_GPT0_GTCIV0=0x16,IER_GPT0_LOCO1=0x16,
IER_GPT1_GTCIA1=0x16,IER_GPT1_GTCIB1=0x16,IER_GPT1_GTCIC1=0x16,IER_GPT1_GTCIE1=0x16,IER_GPT1_GTCIV1=0x17,
IER_GPT2_GTCIA2=0x17,IER_GPT2_GTCIB2=0x17,IER_GPT2_GTCIC2=0x17,IER_GPT2_GTCIE2=0x17,IER_GPT2_GTCIV2=0x17,
IER_GPT3_GTCIA3=0x18,IER_GPT3_GTCIB3=0x18,IER_GPT3_GTCIC3=0x18,IER_GPT3_GTCIE3=0x18,IER_GPT3_GTCIV3=0x18,
IER_SCI0_ERI0=0x1A,IER_SCI0_RXI0=0x1A,IER_SCI0_TXI0=0x1B,IER_SCI0_TEI0=0x1B,
IER_SCI1_ERI1=0x1B,IER_SCI1_RXI1=0x1B,IER_SCI1_TXI1=0x1B,IER_SCI1_TEI1=0x1B,
IER_SCI2_ERI2=0x1B,IER_SCI2_RXI2=0x1B,IER_SCI2_TXI2=0x1C,IER_SCI2_TEI2=0x1C,
IER_RIIC0_ICEEI0=0x1E,IER_RIIC0_ICRXI0=0x1E,IER_RIIC0_ICTXI0=0x1F,IER_RIIC0_ICTEI0=0x1F,
IER_LIN0_LIN0=0x1F
};

enum enum_ipr {
IPR_BSC_BUSERR=0x00,
IPR_FCU_FIFERR=0x01,IPR_FCU_FRDYI=0x02,
IPR_ICU_SWINT=0x03,
IPR_CMT0_CMI0=0x04,
IPR_CMT1_CMI1=0x05,
IPR_CMT2_CMI2=0x06,
IPR_CMT3_CMI3=0x07,
IPR_RSPI0_SPEI0=0x14,IPR_RSPI0_SPRI0=0x14,IPR_RSPI0_SPTI0=0x14,IPR_RSPI0_SPII0=0x14,
IPR_CAN0_ERS0=0x18,IPR_CAN0_RXF0=0x18,IPR_CAN0_TXF0=0x18,IPR_CAN0_RXM0=0x18,IPR_CAN0_TXM0=0x18,
IPR_ICU_IRQ0=0x20,IPR_ICU_IRQ1=0x21,IPR_ICU_IRQ2=0x22,IPR_ICU_IRQ3=0x23,IPR_ICU_IRQ4=0x24,IPR_ICU_IRQ5=0x25,IPR_ICU_IRQ6=0x26,IPR_ICU_IRQ7=0x27,
IPR_WDT_WOVI=0x40,
IPR_AD0_ADI0=0x44,
IPR_S12AD0_S12ADI0=0x48,
IPR_S12AD1_S12ADI1=0x48,
IPR_S12AD_CMPI=0x49,
IPR_MTU0_TGIA0=0x51,IPR_MTU0_TGIB0=0x51,IPR_MTU0_TGIC0=0x51,IPR_MTU0_TGID0=0x51,IPR_MTU0_TCIV0=0x52,IPR_MTU0_TGIE0=0x52,IPR_MTU0_TGIF0=0x52,
IPR_MTU1_TGIA1=0x53,IPR_MTU1_TGIB1=0x53,IPR_MTU1_TCIV1=0x54,IPR_MTU1_TCIU1=0x54,
IPR_MTU2_TGIA2=0x55,IPR_MTU2_TGIB2=0x55,IPR_MTU2_TCIV2=0x56,IPR_MTU2_TCIU2=0x56,
IPR_MTU3_TGIA3=0x57,IPR_MTU3_TGIB3=0x57,IPR_MTU3_TGIC3=0x57,IPR_MTU3_TGID3=0x57,IPR_MTU3_TCIV3=0x58,
IPR_MTU4_TGIA4=0x59,IPR_MTU4_TGIB4=0x59,IPR_MTU4_TGIC4=0x59,IPR_MTU4_TGID4=0x59,IPR_MTU4_TCIV4=0x5A,
IPR_MTU5_TGIU5=0x5B,IPR_MTU5_TGIV5=0x5B,IPR_MTU5_TGIW5=0x5B,
IPR_MTU6_TGIA6=0x5C,IPR_MTU6_TGIB6=0x5C,IPR_MTU6_TGIC6=0x5C,IPR_MTU6_TGID6=0x5C,IPR_MTU6_TCIV6=0x5D,
IPR_MTU7_TGIA7=0x5E,IPR_MTU7_TGIB7=0x5E,IPR_MTU7_TGIC7=0x5F,IPR_MTU7_TGID7=0x5F,IPR_MTU7_TCIV7=0x60,
IPR_POE_OEI1=0x67,IPR_POE_OEI2=0x67,IPR_POE_OEI3=0x67,IPR_POE_OEI4=0x67,
IPR_GPT0_GTCIA0=0x68,IPR_GPT0_GTCIB0=0x68,IPR_GPT0_GTCIC0=0x68,IPR_GPT0_GTCIE0=0x69,IPR_GPT0_GTCIV0=0x69,IPR_GPT0_LOCO1=0x69,
IPR_GPT1_GTCIA1=0x6A,IPR_GPT1_GTCIB1=0x6A,IPR_GPT1_GTCIC1=0x6A,IPR_GPT1_GTCIE1=0x6B,IPR_GPT1_GTCIV1=0x6B,
IPR_GPT2_GTCIA2=0x6C,IPR_GPT2_GTCIB2=0x6C,IPR_GPT2_GTCIC2=0x6C,IPR_GPT2_GTCIE2=0x6D,IPR_GPT2_GTCIV2=0x6D,
IPR_GPT3_GTCIA3=0x6E,IPR_GPT3_GTCIB3=0x6E,IPR_GPT3_GTCIC3=0x6E,IPR_GPT3_GTCIE3=0x6F,IPR_GPT3_GTCIV3=0x6F,
IPR_SCI0_ERI0=0x80,IPR_SCI0_RXI0=0x80,IPR_SCI0_TXI0=0x80,IPR_SCI0_TEI0=0x80,
IPR_SCI1_ERI1=0x81,IPR_SCI1_RXI1=0x81,IPR_SCI1_TXI1=0x81,IPR_SCI1_TEI1=0x81,
IPR_SCI2_ERI2=0x82,IPR_SCI2_RXI2=0x82,IPR_SCI2_TXI2=0x82,IPR_SCI2_TEI2=0x82,
IPR_RIIC0_ICEEI0=0x88,IPR_RIIC0_ICRXI0=0x89,IPR_RIIC0_ICTXI0=0x8A,IPR_RIIC0_ICTEI0=0x8B,
IPR_LIN0_LIN0=0x90,
IPR_BSC_=0x00
};

#define	IEN_BSC_BUSERR		IEN0
#define	IEN_FCU_FIFERR	IEN5
#define	IEN_FCU_FRDYI		IEN7
#define	IEN_ICU_SWINT		IEN3
#define	IEN_CMT0_CMI0		IEN4
#define	IEN_CMT1_CMI1		IEN5
#define	IEN_CMT2_CMI2		IEN6
#define	IEN_CMT3_CMI3		IEN7
#define	IEN_RSPI0_SPEI0		IEN4
#define	IEN_RSPI0_SPRI0		IEN5
#define	IEN_RSPI0_SPTI0		IEN6
#define	IEN_RSPI0_SPII0		IEN7
#define	IEN_CAN0_ERS0		IEN0
#define	IEN_CAN0_RXF0		IEN1
#define	IEN_CAN0_TXF0		IEN2
#define	IEN_CAN0_RXM0		IEN3
#define	IEN_CAN0_TXM0		IEN4
#define	IEN_ICU_IRQ0		IEN0
#define	IEN_ICU_IRQ1		IEN1
#define	IEN_ICU_IRQ2		IEN2
#define	IEN_ICU_IRQ3		IEN3
#define	IEN_ICU_IRQ4		IEN4
#define	IEN_ICU_IRQ5		IEN5
#define	IEN_ICU_IRQ6		IEN6
#define	IEN_ICU_IRQ7		IEN7
#define	IEN_WDT_WOVI		IEN0
#define	IEN_AD0_ADI0		IEN2
#define	IEN_S12AD0_S12ADI0	IEN6
#define	IEN_S12AD1_S12ADI1	IEN7
#define	IEN_S12AD_CMPI		IEN2
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
#define	IEN_MTU5_TGIW5		IEN5
#define	IEN_MTU6_TGIA6		IEN6
#define	IEN_MTU6_TGIB6		IEN7
#define	IEN_MTU6_TGIC6		IEN0
#define	IEN_MTU6_TGID6		IEN1
#define	IEN_MTU6_TCIV6		IEN2
#define	IEN_MTU7_TGIA7		IEN5
#define	IEN_MTU7_TGIB7		IEN6
#define	IEN_MTU7_TGIC7		IEN7
#define	IEN_MTU7_TGID7		IEN0
#define	IEN_MTU7_TCIV7		IEN1
#define	IEN_POE_OEI1		IEN2
#define	IEN_POE_OEI2		IEN3
#define	IEN_POE_OEI3		IEN4
#define	IEN_POE_OEI4		IEN5
#define	IEN_GPT0_GTCIA0		IEN6
#define	IEN_GPT0_GTCIB0		IEN7
#define	IEN_GPT0_GTCIC0		IEN0
#define	IEN_GPT0_GTCIE0		IEN1
#define	IEN_GPT0_GTCIV0		IEN2
#define	IEN_GPT0_LOCO1		IEN3
#define	IEN_GPT1_GTCIA1		IEN4
#define	IEN_GPT1_GTCIB1		IEN5
#define	IEN_GPT1_GTCIC1		IEN6
#define	IEN_GPT1_GTCIE1		IEN7
#define	IEN_GPT1_GTCIV1		IEN0
#define	IEN_GPT2_GTCIA2		IEN2
#define	IEN_GPT2_GTCIB2		IEN3
#define	IEN_GPT2_GTCIC2		IEN4
#define	IEN_GPT2_GTCIE2		IEN5
#define	IEN_GPT2_GTCIV2		IEN6
#define	IEN_GPT3_GTCIA3		IEN0
#define	IEN_GPT3_GTCIB3		IEN1
#define	IEN_GPT3_GTCIC3		IEN2
#define	IEN_GPT3_GTCIE3		IEN3
#define	IEN_GPT3_GTCIV3		IEN4
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
#define	IEN_RIIC0_ICEEI0	IEN6
#define	IEN_RIIC0_ICRXI0	IEN7
#define	IEN_RIIC0_ICTXI0	IEN0
#define	IEN_RIIC0_ICTEI0	IEN1
#define	IEN_LIN0_LIN0		IEN6

#define	VECT_BSC_BUSERR		16
#define	VECT_FCU_FIFERR	21
#define	VECT_FCU_FRDYI	23
#define	VECT_ICU_SWINT		27
#define	VECT_CMT0_CMI0		28
#define	VECT_CMT1_CMI1		29
#define	VECT_CMT2_CMI2		30
#define	VECT_CMT3_CMI3		31
#define	VECT_RSPI0_SPEI0	44
#define	VECT_RSPI0_SPRI0	45
#define	VECT_RSPI0_SPTI0	46
#define	VECT_RSPI0_SPII0	47
#define	VECT_CAN0_ERS0		56
#define	VECT_CAN0_RXF0		57
#define	VECT_CAN0_TXF0		58
#define	VECT_CAN0_RXM0		59
#define	VECT_CAN0_TXM0		60
#define	VECT_ICU_IRQ0		64
#define	VECT_ICU_IRQ1		65
#define	VECT_ICU_IRQ2		66
#define	VECT_ICU_IRQ3		67
#define	VECT_ICU_IRQ4		68
#define	VECT_ICU_IRQ5		69
#define	VECT_ICU_IRQ6		70
#define	VECT_ICU_IRQ7		71
#define	VECT_WDT_WOVI		96
#define	VECT_AD0_ADI0		98
#define	VECT_S12AD0_S12ADI0	102
#define	VECT_S12AD1_S12ADI1	103
#define	VECT_S12AD_CMPI		106
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
#define	VECT_MTU7_TGIA7		149
#define	VECT_MTU7_TGIB7		150
#define	VECT_MTU7_TGIC7		151
#define	VECT_MTU7_TGID7		152
#define	VECT_MTU7_TCIV7		153
#define	VECT_POE_OEI1		170
#define	VECT_POE_OEI2		171
#define	VECT_POE_OEI3		172
#define	VECT_POE_OEI4		173
#define	VECT_GPT0_GTCIA0	174
#define	VECT_GPT0_GTCIB0	175
#define	VECT_GPT0_GTCIC0	176
#define	VECT_GPT0_GTCIE0	177
#define	VECT_GPT0_GTCIV0	178
#define	VECT_GPT0_LOCO1		179
#define	VECT_GPT1_GTCIA1	180
#define	VECT_GPT1_GTCIB1	181
#define	VECT_GPT1_GTCIC1	182
#define	VECT_GPT1_GTCIE1	183
#define	VECT_GPT1_GTCIV1	184
#define	VECT_GPT2_GTCIA2	186
#define	VECT_GPT2_GTCIB2	187
#define	VECT_GPT2_GTCIC2	188
#define	VECT_GPT2_GTCIE2	189
#define	VECT_GPT2_GTCIV2	190
#define	VECT_GPT3_GTCIA3	192
#define	VECT_GPT3_GTCIB3	193
#define	VECT_GPT3_GTCIC3	194
#define	VECT_GPT3_GTCIE3	195
#define	VECT_GPT3_GTCIV3	196
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
#define	VECT_RIIC0_ICEEI0	246
#define	VECT_RIIC0_ICRXI0	247
#define	VECT_RIIC0_ICTXI0	248
#define	VECT_RIIC0_ICTEI0	249
#define	VECT_LIN0_LIN0		254

#define	MSTP_DTC	SYSTEM.MSTPCRA.BIT.MSTPA28
#define	MSTP_S12AD	SYSTEM.MSTPCRA.BIT.MSTPA24
#define	MSTP_AD0	SYSTEM.MSTPCRA.BIT.MSTPA23
#define	MSTP_S12AD0	SYSTEM.MSTPCRA.BIT.MSTPA17
#define	MSTP_S12AD1	SYSTEM.MSTPCRA.BIT.MSTPA16
#define	MSTP_CMT0	SYSTEM.MSTPCRA.BIT.MSTPA15
#define	MSTP_CMT1	SYSTEM.MSTPCRA.BIT.MSTPA15
#define	MSTP_CMT2	SYSTEM.MSTPCRA.BIT.MSTPA14
#define	MSTP_CMT3	SYSTEM.MSTPCRA.BIT.MSTPA14
#define	MSTP_MTU	SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU0	SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU1	SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU2	SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU3	SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU4	SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU5	SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU6	SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_MTU7	SYSTEM.MSTPCRA.BIT.MSTPA9
#define	MSTP_GPT	SYSTEM.MSTPCRA.BIT.MSTPA7
#define	MSTP_GPT0	SYSTEM.MSTPCRA.BIT.MSTPA7
#define	MSTP_GPT1	SYSTEM.MSTPCRA.BIT.MSTPA7
#define	MSTP_GPT2	SYSTEM.MSTPCRA.BIT.MSTPA7
#define	MSTP_GPT3	SYSTEM.MSTPCRA.BIT.MSTPA7
#define	MSTP_SCI0	SYSTEM.MSTPCRB.BIT.MSTPB31
#define	MSTP_SMCI0	SYSTEM.MSTPCRB.BIT.MSTPB31
#define	MSTP_SCI1	SYSTEM.MSTPCRB.BIT.MSTPB30
#define	MSTP_SMCI1	SYSTEM.MSTPCRB.BIT.MSTPB30
#define	MSTP_SCI2	SYSTEM.MSTPCRB.BIT.MSTPB29
#define	MSTP_SMCI2	SYSTEM.MSTPCRB.BIT.MSTPB29
#define	MSTP_CRC	SYSTEM.MSTPCRB.BIT.MSTPB23
#define	MSTP_RIIC0	SYSTEM.MSTPCRB.BIT.MSTPB21
#define	MSTP_RSPI0	SYSTEM.MSTPCRB.BIT.MSTPB17
#define	MSTP_LIN0	SYSTEM.MSTPCRB.BIT.MSTPB7
#define	MSTP_CAN0	SYSTEM.MSTPCRB.BIT.MSTPB0
#define	MSTP_RAM	SYSTEM.MSTPCRC.BIT.MSTPC0

#define	UT7AE		UT4AE
#define	DT7AE		DT4AE
#define	UT7BE		UT4BE
#define	DT7BE		DT4BE
#define	ITA6AE		ITA3AE
#define	ITA7VE		ITA4VE
#define	ITB6AE		ITB3AE
#define	ITB7VE		ITB4VE
#define	PG102SEL	PG002SEL
#define	PG101SEL	PG001SEL
#define	PG100SEL	PG000SEL
#define	PG102EN		PG002EN
#define	PG101EN		PG001EN
#define	PG100EN		PG000EN
#define	PG102GAIN	PG002GAIN
#define	PG101GAIN	PG001GAIN
#define	PG100GAIN	PG000GAIN

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

#define	AD0		(*(volatile struct st_ad     __evenaccess *)0x88040)
#define	BSC		(*(volatile struct st_bsc    __evenaccess *)0x81300)
#define	CAN0	(*(volatile struct st_can    __evenaccess *)0x90200)
#define	CMT		(*(volatile struct st_cmt    __evenaccess *)0x88000)
#define	CMT0	(*(volatile struct st_cmt0   __evenaccess *)0x88002)
#define	CMT1	(*(volatile struct st_cmt0   __evenaccess *)0x88008)
#define	CMT2	(*(volatile struct st_cmt0   __evenaccess *)0x88012)
#define	CMT3	(*(volatile struct st_cmt0   __evenaccess *)0x88018)
#define	CRC		(*(volatile struct st_crc    __evenaccess *)0x88280)
#define	DTC		(*(volatile struct st_dtc    __evenaccess *)0x82400)
#define	FLASH	(*(volatile struct st_flash  __evenaccess *)0x8C288)
#define	GPT		(*(volatile struct st_gpt    __evenaccess *)0xC2000)
#define	GPT0	(*(volatile struct st_gpt0   __evenaccess *)0xC2100)
#define	GPT1	(*(volatile struct st_gpt0   __evenaccess *)0xC2180)
#define	GPT2	(*(volatile struct st_gpt0   __evenaccess *)0xC2200)
#define	GPT3	(*(volatile struct st_gpt0   __evenaccess *)0xC2280)
#define	ICU		(*(volatile struct st_icu    __evenaccess *)0x87000)
#define	IOPORT	(*(volatile struct st_ioport __evenaccess *)0x8C108)
#define	IWDT	(*(volatile struct st_iwdt   __evenaccess *)0x88030)
#define	LIN0	(*(volatile struct st_lin    __evenaccess *)0x94001)
#define	MTU		(*(volatile struct st_mtu    __evenaccess *)0xC120A)
#define	MTU0	(*(volatile struct st_mtu0   __evenaccess *)0xC1300)
#define	MTU1	(*(volatile struct st_mtu1   __evenaccess *)0xC1380)
#define	MTU2	(*(volatile struct st_mtu2   __evenaccess *)0xC1400)
#define	MTU3	(*(volatile struct st_mtu3   __evenaccess *)0xC1200)
#define	MTU4	(*(volatile struct st_mtu4   __evenaccess *)0xC1200)
#define	MTU5	(*(volatile struct st_mtu5   __evenaccess *)0xC1C80)
#define	MTU6	(*(volatile struct st_mtu3   __evenaccess *)0xC1A00)
#define	MTU7	(*(volatile struct st_mtu4   __evenaccess *)0xC1A00)
#define	POE		(*(volatile struct st_poe    __evenaccess *)0x8C4C0)
#define	PORT1	(*(volatile struct st_port1  __evenaccess *)0x8C001)
#define	PORT2	(*(volatile struct st_port2  __evenaccess *)0x8C002)
#define	PORT3	(*(volatile struct st_port3  __evenaccess *)0x8C003)
#define	PORT4	(*(volatile struct st_port4  __evenaccess *)0x8C044)
#define	PORT5	(*(volatile struct st_port5  __evenaccess *)0x8C045)
#define	PORT6	(*(volatile struct st_port6  __evenaccess *)0x8C046)
#define	PORT7	(*(volatile struct st_port7  __evenaccess *)0x8C007)
#define	PORT8	(*(volatile struct st_port8  __evenaccess *)0x8C008)
#define	PORT9	(*(volatile struct st_port9  __evenaccess *)0x8C009)
#define	PORTA	(*(volatile struct st_porta  __evenaccess *)0x8C00A)
#define	PORTB	(*(volatile struct st_portb  __evenaccess *)0x8C00B)
#define	PORTD	(*(volatile struct st_portd  __evenaccess *)0x8C00D)
#define	PORTE	(*(volatile struct st_porte  __evenaccess *)0x8C00E)
#define	PORTG	(*(volatile struct st_portg  __evenaccess *)0x8C010)
#define	RIIC0	(*(volatile struct st_riic   __evenaccess *)0x88300)
#define	RSPI0	(*(volatile struct st_rspi   __evenaccess *)0x88380)
#define	S12AD	(*(volatile struct st_s12ad  __evenaccess *)0x89012)
#define	S12AD0	(*(volatile struct st_s12ad0 __evenaccess *)0x89000)
#define	S12AD1	(*(volatile struct st_s12ad0 __evenaccess *)0x89080)
#define	SCI0	(*(volatile struct st_sci    __evenaccess *)0x88240)
#define	SCI1	(*(volatile struct st_sci    __evenaccess *)0x88248)
#define	SCI2	(*(volatile struct st_sci    __evenaccess *)0x88250)
#define	SMCI0	(*(volatile struct st_smci   __evenaccess *)0x88240)
#define	SMCI1	(*(volatile struct st_smci   __evenaccess *)0x88248)
#define	SMCI2	(*(volatile struct st_smci   __evenaccess *)0x88250)
#define	SYSTEM	(*(volatile struct st_system __evenaccess *)0x80000)
#define	WDT		(*(volatile union un_wdt     __evenaccess *)0x88028)
#pragma bit_order
#pragma packoption
#endif