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
* File Name     : spibsc_iodefine.h 
* Version       : 0.01
* Device(s)     : 
* Tool-Chain    : DS-5 Ver 5.8
*                 ARM Complier 
*               : 
* H/W Platform  : CPU Board
* Description   : 
*******************************************************************************/
/*******************************************************************************
* History : 05.11.2012 0.01 Version Description
*******************************************************************************/
#ifndef __SPIBSC_IODEFINE_H__
#define __SPIBSC_IODEFINE_H__

#include "typedefine.h"


/****************************************************************/
/*       SPIBSC                                                 */
/****************************************************************/
struct st_spibsc_n {                              /* struct SPIBSC*/
       union {                                  /* CMNCR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD BSZ:2;              /*   BSZ        */
                    _UDWORD :1;                 /*              */
                    _UDWORD CPOL:1;             /*   CPOL       */
                    _UDWORD SSLP:1;             /*   SSLP       */
                    _UDWORD CPHAR:1;            /*   CPHAR      */
                    _UDWORD CPHAT:1;            /*   CPHAT      */
                    _UDWORD :1;                 /*              */
                    _UDWORD IO0FV:2;            /*   IO0FV      */
                    _UDWORD :2;                 /*              */
                    _UDWORD IO2FV:2;            /*   IO2FV      */
                    _UDWORD IO3FV:2;            /*   IO3FV      */
                    _UDWORD MOIIO0:2;           /*   MOIIO0     */
                    _UDWORD MOIIO1:2;           /*   MOIIO1     */
                    _UDWORD MOIIO2:2;           /*   MOIIO2     */
                    _UDWORD MOIIO3:2;           /*   MOIIO3     */
                    _UDWORD :7;                 /*              */
                    _UDWORD MD:1;               /*   MD         */
                    } BIT;                      /*              */
             } CMNCR;                           /*              */
       union {                                  /* SSLDR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD SCKDL:3;            /*   SCKDL      */
                    _UDWORD :5;                 /*              */
                    _UDWORD SLNDL:3;            /*   SLNDL      */
                    _UDWORD :5;                 /*              */
                    _UDWORD SPNDL:3;            /*   SPNDL      */
                    _UDWORD :13;                /*              */
                    } BIT;                      /*              */
             } SSLDR;                           /*              */
       union {                                  /* SPBCR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD BRDV:2;             /*   BRDV       */
                    _UDWORD :6;                 /*              */
                    _UDWORD SPBR:8;             /*   SPBR       */
                    _UDWORD :16;                /*              */
                    } BIT;                      /*              */
             } SPBCR;                           /*              */
       union {                                  /* DRCR         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD SSLE:1;             /*   SSLE       */
                    _UDWORD :7;                 /*              */
                    _UDWORD RBE:1;              /*   RBE        */
                    _UDWORD RCF:1;              /*   RCF        */
                    _UDWORD :6;                 /*              */
                    _UDWORD RBURST:4;           /*   RBURST     */
                    _UDWORD :4;                 /*              */
                    _UDWORD SSLN:1;             /*   SSLN       */
                    _UDWORD :7;                 /*              */
                    } BIT;                      /*              */
             } DRCR;                            /*              */
       union {                                  /* DRCMR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD OCMD:8;             /*   OCMD       */
                    _UDWORD :8;                 /*              */
                    _UDWORD CMD:8;              /*   CMD        */
                    _UDWORD :8;                 /*              */
                    } BIT;                      /*              */
             } DRCMR;                           /*              */
       union {                                  /* DREAR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD EAC:3;              /*   EAC        */
                    _UDWORD :13;                /*              */
                    _UDWORD EAV:8;              /*   EAV        */
                    _UDWORD :8;                 /*              */
                    } BIT;                      /*              */
             } DREAR;                           /*              */
       union {                                  /* DROPR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD OPD0:8;             /*   OPD0       */
                    _UDWORD OPD1:8;             /*   OPD1       */
                    _UDWORD OPD2:8;             /*   OPD2       */
                    _UDWORD OPD3:8;             /*   OPD3       */
                    } BIT;                      /*              */
             } DROPR;                           /*              */
       union {                                  /* DRENR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :4;                 /*              */
                    _UDWORD OPDE:4;             /*   OPDE       */
                    _UDWORD ADE:4;              /*   ADE        */
                    _UDWORD OCDE:1;             /*   OCDE       */
                    _UDWORD :1;                 /*              */
                    _UDWORD CDE:1;              /*   CDE        */
                    _UDWORD DME:1;              /*   DME        */
                    _UDWORD DRDB:2;             /*   DRDB       */
                    _UDWORD :2;                 /*              */
                    _UDWORD OPDB:2;             /*   OPDB       */
                    _UDWORD :2;                 /*              */
                    _UDWORD ADB:2;              /*   ADB        */
                    _UDWORD :2;                 /*              */
                    _UDWORD OCDB:2;             /*   OCDB       */
                    _UDWORD CDB:2;              /*   CDB        */
                    } BIT;                      /*              */
             } DRENR;                           /*              */
       union {                                  /* SMCR         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD SPIE:1;             /*   SPIE       */
                    _UDWORD SPIWE:1;            /*   SPIWE      */
                    _UDWORD SPIRE:1;            /*   SPIRE      */
                    _UDWORD :5;                 /*              */
                    _UDWORD SSLKP:1;            /*   SSLKP      */
                    _UDWORD :23;                /*              */
                    } BIT;                      /*              */
             } SMCR;                            /*              */
       union {                                  /* SMCMR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD OCMD:8;             /*   OCMD       */
                    _UDWORD :8;                 /*              */
                    _UDWORD CMD:8;              /*   CMD        */
                    _UDWORD :8;                 /*              */
                    } BIT;                      /*              */
             } SMCMR;                           /*              */
       union {                                  /* SMADR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD ADR:32;             /*   ADR        */
                    } BIT;                      /*              */
             } SMADR;                           /*              */
       union {                                  /* SMOPR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD OPD0:8;             /*   OPD0       */
                    _UDWORD OPD1:8;             /*   OPD1       */
                    _UDWORD OPD2:8;             /*   OPD2       */
                    _UDWORD OPD3:8;             /*   OPD3       */
                    } BIT;                      /*              */
             } SMOPR;                           /*              */
       union {                                  /* SMENR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD SPIDE:4;            /*   SPIDE      */
                    _UDWORD OPDE:4;             /*   OPDE       */
                    _UDWORD ADE:4;              /*   ADE        */
                    _UDWORD OCDE:1;             /*   OCDE       */
                    _UDWORD :1;                 /*              */
                    _UDWORD CDE:1;              /*   CDE        */
                    _UDWORD DME:1;              /*   DME        */
                    _UDWORD SPIDB:2;            /*   SPIDB      */
                    _UDWORD :2;                 /*              */
                    _UDWORD OPDB:2;             /*   OPDB       */
                    _UDWORD :2;                 /*              */
                    _UDWORD ADB:2;              /*   ADB        */
                    _UDWORD :2;                 /*              */
                    _UDWORD OCDB:2;             /*   OCDB       */
                    _UDWORD CDB:2;              /*   CDB        */
                    } BIT;                      /*              */
             } SMENR;                           /*              */
       _UBYTE wk0[4];                           /*              */
       union {                                  /* SMRDR0       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD L;                   /*   Low        */
                    _UWORD H;                   /*   High       */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE LL;                  /*   Low, Low   */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE HH;                  /*   High, High */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD RDATA0:32;          /*   RDATA0     */
                    } BIT;                      /*              */
             } SMRDR0;                          /*              */
       union {                                  /* SMRDR1       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD L;                   /*   Low        */
                    _UWORD H;                   /*   High       */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE LL;                  /*   Low, Low   */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE HH;                  /*   High, High */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD RDATA1:32;          /*   RDATA1     */
                    } BIT;                      /*              */
             } SMRDR1;                          /*              */
       union {                                  /* SMWDR0       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD L;                   /*   Low        */
                    _UWORD H;                   /*   High       */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE LL;                  /*   Low, Low   */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE HH;                  /*   High, High */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD WDATA0:32;          /*   WDATA0     */
                    } BIT;                      /*              */
             } SMWDR0;                          /*              */
       union {                                  /* SMWDR1       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Word Access */
                    _UWORD L;                   /*   Low        */
                    _UWORD H;                   /*   High       */
                    } WORD;                     /*              */
             struct {                           /*  Byte Access */
                    _UBYTE LL;                  /*   Low, Low   */
                    _UBYTE LH;                  /*   Low, High  */
                    _UBYTE HL;                  /*   High, Low  */
                    _UBYTE HH;                  /*   High, High */
                    } BYTE;                     /*              */
             struct {                           /*  Bit Access  */
                    _UDWORD WDATA1:32;          /*   WDATA1     */
                    } BIT;                      /*              */
             } SMWDR1;                          /*              */
       union {                                  /* CMNSR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD TEND:1;             /*   TEND       */
                    _UDWORD SSLF:1;             /*   SSLF       */
                    _UDWORD :30;                /*              */
                    } BIT;                      /*              */
             } CMNSR;                           /*              */
       _UBYTE wk1[12];                          /*              */
      union {                                   /* DRDMCR       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
            	     _UDWORD DMCYC:3;           /*              */
            	 	 _UDWORD :13;               /*              */
            	 	 _UDWORD DMDB:2;            /*              */
            	 	 _UDWORD :14;               /*              */
                    } BIT;                      /*              */
             } DRDMCR;                          /*              */
      union {                                   /* DRDRENR      */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                     _UDWORD DRDRE:1;           /*              */
                     _UDWORD :3;                /*              */
                     _UDWORD OPDRE:1;           /*              */
        	 	     _UDWORD :3;                /*              */
                     _UDWORD ADDRE:1;           /*              */
                     _UDWORD :23;               /*              */
                    } BIT;                      /*              */
             } DRDRENR;                         /*              */

      union {                                   /* SMDMCR       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                     _UDWORD DMCYC:3;           /*              */
                     _UDWORD :13;               /*              */
                     _UDWORD DMDB:2;            /*              */
                     _UDWORD :14;               /*              */
                    } BIT;                      /*              */
             } SMDMCR;                          /*              */
      union {                                   /* SMDRENR      */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                     _UDWORD SPIDRE:1;          /*              */
                     _UDWORD :3;                /*              */
                     _UDWORD OPDRE:1;           /*              */
    	 	         _UDWORD :3;                /*              */
                     _UDWORD ADDRE:1;           /*              */
                     _UDWORD :23;               /*              */
                    } BIT;                      /*              */
             } SMDRENR;                         /*              */
};                                              /*              */

#define SPIBSC0 (*(volatile struct st_spibsc_n *)0x3FEFA000)
#define SPIBSC1 (*(volatile struct st_spibsc_n *)0x3FEFB000)


#endif /* __SPIBSC_IODEFINE_H__ */
