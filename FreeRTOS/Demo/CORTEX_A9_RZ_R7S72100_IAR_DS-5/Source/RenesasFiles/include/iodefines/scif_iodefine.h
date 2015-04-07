/******************************************************************************
*   DISCLAIMER
*
*   This software is supplied by Renesas Electronics Corporation and is only 
*   intended for use with Renesas products. No other uses are authorized.
*
*   This software is owned by Renesas Electronics Corporation and is protected under 
*   all applicable laws, including copyright laws.
*
*   THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES 
*   REGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, 
*   INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A 
*   PARTICULAR PURPOSE AND NON-INFRINGEMENT.  ALL SUCH WARRANTIES ARE EXPRESSLY 
*   DISCLAIMED.
*
*   TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS 
*   ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE 
*   FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES 
*   FOR ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR ITS
*   AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
*
*   Renesas reserves the right, without notice, to make changes to this 
*   software and to discontinue the availability of this software.
*   By using this software, you agree to the additional terms and 
*   conditions found by accessing the following link: 
*   http://www.renesas.com/disclaimer
********************************************************************************
*   Copyright (C) 2012 Renesas Electronics Corporation. All rights reserved.
**************************** Technical reference data **************************
*   System Name : 
*   File Name   : scif_iodefine.h
*   Abstract    : 
*   Version     : 1.00.00
*   Device      : ARM
*   Tool-Chain  : 
*   OS          : None
*   H/W Platform: 
*   Description : 
********************************************************************************
*   History     : Mar.06,2012 Ver.1.00.00
*******************************************************************************/
#ifndef __SCIF_IODEFINE_H__
#define __SCIF_IODEFINE_H__

#include "typedefine.h"

struct st_scif_n {                              /* struct SCIF  */
       union {                                  /* SCSMR_0      */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD CKS:2;               /*   CKS        */
                    _UWORD :1;                  /*              */
                    _UWORD STOP:1;              /*   STOP       */
                    _UWORD OE:1;                /*   O/E        */
                    _UWORD PE:1;                /*   PE         */
                    _UWORD CHR:1;               /*   CHR        */
                    _UWORD CA:1;                /*   C/A        */
                    _UWORD :8;                  /*              */
                    } BIT;                      /*              */
             } SCSMR;                           /*              */
       _UBYTE wk0[2];                           /*              */
       union {                                  /* SCBRR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE D:8;                 /*   D          */
                    } BIT;                      /*              */
             } SCBRR;                           /*              */
       _UBYTE wk1[3];                           /*              */
       union {                                  /* SCSCR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD CKE:2;               /*   CKE        */
                    _UWORD :1;                  /*              */
                    _UWORD REIE:1;              /*   REIE       */
                    _UWORD RE:1;                /*   RE         */
                    _UWORD TE:1;                /*   TE         */
                    _UWORD RIE:1;               /*   RIE        */
                    _UWORD TIE:1;               /*   TIE        */
                    _UWORD :8;                  /*              */
                    } BIT;                      /*              */
             } SCSCR;                           /*              */
       _UBYTE wk2[2];                           /*              */
       union {                                  /* SCFTDR       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE D:8;                 /*   D          */
                    } BIT;                      /*              */
             } SCFTDR;                          /*              */
       _UBYTE wk3[3];                           /*              */
       union {                                  /* SCFSR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD DR:1;                /*   DR         */
                    _UWORD RDF:1;               /*   RDF        */
                    _UWORD PER:1;               /*   PER        */
                    _UWORD FER:1;               /*   FER        */
                    _UWORD BRK:1;               /*   BRK        */
                    _UWORD TDFE:1;              /*   TDFE       */
                    _UWORD TEND:1;              /*   TEND       */
                    _UWORD ER:1;                /*   ER         */
                    _UWORD FERN:4;              /*   FERN       */
                    _UWORD PERN:4;              /*   PERN       */
                    } BIT;                      /*              */
             } SCFSR;                           /*              */
       _UBYTE wk4[2];                           /*              */
       union {                                  /* SCFRDR       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE D:8;                 /*   D          */
                    } BIT;                      /*              */
             } SCFRDR;                          /*              */
       _UBYTE wk5[3];                           /*              */
       union {                                  /* SCFCR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD LOOP:1;              /*   LOOP       */
                    _UWORD RFRST:1;             /*   RFRST      */
                    _UWORD TFRST:1;             /*   TFRST      */
                    _UWORD MCE:1;               /*   MCE        */
                    _UWORD TTRG:2;              /*   TTRG       */
                    _UWORD RTRG:2;              /*   RTRG       */
                    _UWORD RSTRG:3;             /*   RSTRG      */
                    _UWORD :5;                  /*              */
                    } BIT;                      /*              */
             } SCFCR;                           /*              */
       _UBYTE wk6[2];                           /*              */
       union {                                  /* SCFDR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD R:5;                 /*   R          */
                    _UWORD :3;                  /*              */
                    _UWORD T:5;                 /*   T          */
                    _UWORD :3;                  /*              */
                    } BIT;                      /*              */
             } SCFDR;                           /*              */
       _UBYTE wk7[2];                           /*              */
       union {                                  /* SCSPTR       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD SPB2DT:1;            /*   SPB2DT     */
                    _UWORD SPB2IO:1;            /*   SPB2IO     */
                    _UWORD SCKDT:1;             /*   SCKDT      */
                    _UWORD SCKIO:1;             /*   SCKIO      */
                    _UWORD CTSDT:1;             /*   CTSDT      */
                    _UWORD CTSIO:1;             /*   CTSIO      */
                    _UWORD RTSDT:1;             /*   RTSDT      */
                    _UWORD RTSIO:1;             /*   RTSIO      */
                    _UWORD :8;                  /*              */
                    } BIT;                      /*              */
             } SCSPTR;                          /*              */
       _UBYTE wk8[2];                           /*              */
       union {                                  /* SCLSR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD ORER:1;              /*   ORER       */
                    _UWORD :15;                 /*              */
                    } BIT;                      /*              */
             } SCLSR;                           /*              */
       _UBYTE wk9[2];                           /*              */
       union {                                  /* SCEMR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD ABCS:1;              /*   ABCS       */
                    _UWORD :6;                  /*              */
                    _UWORD BGDM:1;              /*   BGDM       */
                    _UWORD :8;                  /*              */
                    } BIT;                      /*              */
             } SCEMR;                           /*              */
};                                              /*              */

#define SCIF0 (*(volatile struct st_scif_n *)0xE8007000)	/* SCIF0 Address */
#define SCIF1 (*(volatile struct st_scif_n *)0xE8007800)	/* SCIF1 Address */
#define SCIF2 (*(volatile struct st_scif_n *)0xE8008000)	/* SCIF2 Address */
#define SCIF3 (*(volatile struct st_scif_n *)0xE8008800)	/* SCIF3 Address */
#define SCIF4 (*(volatile struct st_scif_n *)0xE8009000)	/* SCIF4 Address */
#define SCIF5 (*(volatile struct st_scif_n *)0xE8009800)	/* SCIF5 Address */
#define SCIF6 (*(volatile struct st_scif_n *)0xE800A000)	/* SCIF6 Address */
#define SCIF7 (*(volatile struct st_scif_n *)0xE800A800)	/* SCIF7 Address */


#endif /* __SCIF_IODEFINE_H__ */

/* End of File */
