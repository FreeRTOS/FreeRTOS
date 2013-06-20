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
* File Name     : riic_iodefine.h
* Version       : 0.01
* Device(s)     : Aragon
* Tool-Chain    : DS-5 Ver 5.8
*                 ARM Complier 
*               : 
* H/W Platform  : Aragon CPU Board
* Description   : Aragon Sample Program vecotr.s
*******************************************************************************/
/*******************************************************************************
* History : DD.MM.YYYY Version Description
*         : 27.07.2012 0.01		éQçléëóøÅFRZ_A1H_05J_121010_11.pdf
*******************************************************************************/
#ifndef __RIIC_IODEFINE_H__
#define __RIIC_IODEFINE_H__

#include "typedefine.h"

typedef union {                                 /* RIICnICSARy  */
      _UDWORD LONG;                             /*  Long Access */
      struct {                                  /*  Bit Access  */
             _UDWORD SVA0:1;                    /*   SVA0       */
             _UDWORD SVA:9;                     /*   SVA        */
             _UDWORD :5;                        /*              */
             _UDWORD FSy:1;                     /*   FSy        */
             _UDWORD :16;                       /*              */
             } BIT;                             /*              */
} RIICnICSARy;                                  /*              */

struct st_riic_n {                              /* struct RIIC  */
       union {                                  /* RIICnICCR1   */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD SDAI:1;             /*   SDAI       */
                    _UDWORD SCLI:1;             /*   SCLI       */
                    _UDWORD SDAO:1;             /*   SDAO       */
                    _UDWORD SCLO:1;             /*   SCLO       */
                    _UDWORD SOWP:1;             /*   SOWP       */
                    _UDWORD CLO:1;              /*   CLO        */
                    _UDWORD IICRST:1;           /*   IICRST     */
                    _UDWORD ICE:1;              /*   ICE        */
                    _UDWORD :24;                /*              */
                    } BIT;                      /*              */
             } RIICnICCR1;                      /*              */
       union {                                  /* RIICnICCR2   */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :1;                 /*              */
                    _UDWORD ST:1;               /*   ST         */
                    _UDWORD RS:1;               /*   RS         */
                    _UDWORD SP:1;               /*   SP         */
                    _UDWORD :1;                 /*              */
                    _UDWORD TRS:1;              /*   TRS        */
                    _UDWORD MST:1;              /*   MST        */
                    _UDWORD BBSY:1;             /*   BBSY       */
                    _UDWORD :24;                /*              */
                    } BIT;                      /*              */
             } RIICnICCR2;                      /*              */
       union {                                  /* RIICnICMR1   */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD BC:3;               /*   BC         */
                    _UDWORD BCWP:1;             /*   BCWP       */
                    _UDWORD CKS:3;              /*   CKS        */
                    _UDWORD MTWP:1;             /*   MTWP       */
                    _UDWORD :24;                /*              */
                    } BIT;                      /*              */
             } RIICnICMR1;                      /*              */
       union {                                  /* RIICnICMR2   */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD TMOS:1;             /*   TMOS       */
                    _UDWORD TMOL:1;             /*   TMOL       */
                    _UDWORD TMOH:1;             /*   TMOH       */
                    _UDWORD :1;                 /*              */
                    _UDWORD SDDL:3;             /*   SDDL       */
                    _UDWORD DLCS:1;             /*   DLCS       */
                    _UDWORD :24;                /*              */
                    } BIT;                      /*              */
             } RIICnICMR2;                      /*              */
       union {                                  /* RIICnICMR3   */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD NF:2;               /*   NF         */
                    _UDWORD ACKBR:1;            /*   ACKBR      */
                    _UDWORD ACKBT:1;            /*   ACKBT      */
                    _UDWORD ACKWP:1;            /*   ACKWP      */
                    _UDWORD RDRFS:1;            /*   RDRFS      */
                    _UDWORD WAIT:1;             /*   WAIT       */
                    _UDWORD SMBS:1;             /*   SMBS       */
                    _UDWORD :24;                /*              */
                    } BIT;                      /*              */
             } RIICnICMR3;                      /*              */
       union {                                  /* RIICnICFER   */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD TMOE:1;             /*   TMOE       */
                    _UDWORD MALE:1;             /*   MALE       */
                    _UDWORD NALE:1;             /*   NALE       */
                    _UDWORD SALE:1;             /*   SALE       */
                    _UDWORD NACKE:1;            /*   NACKE      */
                    _UDWORD NFE:1;              /*   NFE        */
                    _UDWORD SCLE:1;             /*   SCLE       */
                    _UDWORD FMPE:1;             /*   FMPE       */
                    _UDWORD :24;                /*              */
                    } BIT;                      /*              */
             } RIICnICFER;                      /*              */
       union {                                  /* RIICnICSER   */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD SAR0E:1;            /*   SAR0E      */
                    _UDWORD SAR1E:1;            /*   SAR1E      */
                    _UDWORD SAR2E:1;            /*   SAR2E      */
                    _UDWORD GCAE:1;             /*   GCAE       */
                    _UDWORD :1;                 /*              */
                    _UDWORD DIDE:1;             /*   DIDE       */
                    _UDWORD :1;                 /*              */
                    _UDWORD HOAE:1;             /*   HOAE       */
                    _UDWORD :24;                /*              */
                    } BIT;                      /*              */
             } RIICnICSER;                      /*              */
       union {                                  /* RIICnICIER   */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD TMOIE:1;            /*   TMOIE      */
                    _UDWORD ALIE:1;             /*   ALIE       */
                    _UDWORD STIE:1;             /*   STIE       */
                    _UDWORD SPIE:1;             /*   SPIE       */
                    _UDWORD NAKIE:1;            /*   NAKIE      */
                    _UDWORD RIE:1;              /*   RIE        */
                    _UDWORD TEIE:1;             /*   TEIE       */
                    _UDWORD TIE:1;              /*   TIE        */
                    _UDWORD :24;                /*              */
                    } BIT;                      /*              */
             } RIICnICIER;                      /*              */
       union {                                  /* RIICnICSR1   */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD AAS0:1;             /*   AAS0       */
                    _UDWORD AAS1:1;             /*   AAS1       */
                    _UDWORD AAS2:1;             /*   AAS2       */
                    _UDWORD GCA:1;              /*   GCA        */
                    _UDWORD :1;                 /*              */
                    _UDWORD DID:1;              /*   DID        */
                    _UDWORD :1;                 /*              */
                    _UDWORD HOA:1;              /*   HOA        */
                    _UDWORD :24;                /*              */
                    } BIT;                      /*              */
             } RIICnICSR1;                      /*              */
       union {                                  /* RIICnICSR2   */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD TMOF:1;             /*   TMOF       */
                    _UDWORD AL:1;               /*   AL         */
                    _UDWORD START:1;            /*   START      */
                    _UDWORD STOP:1;             /*   STOP       */
                    _UDWORD NACKF:1;            /*   NACKF      */
                    _UDWORD RDRF:1;             /*   RDRF       */
                    _UDWORD TEND:1;             /*   TEND       */
                    _UDWORD TDRE:1;             /*   TDRE       */
                    _UDWORD :24;                /*              */
                    } BIT;                      /*              */
             } RIICnICSR2;                      /*              */
		RIICnICSARy RIICnICSAR0;				/* RIICnICSAR0  */
		RIICnICSARy RIICnICSAR1;				/* RIICnICSAR1  */
		RIICnICSARy RIICnICSAR2;				/* RIICnICSAR2  */
       union {                                  /* RIICnICBRL   */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD BRL:5;              /*   BRL        */
                    _UDWORD :27;                /*              */
                    } BIT;                      /*              */
             } RIICnICBRL;                      /*              */
       union {                                  /* RIICnICBRH   */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD BRH:5;              /*   BRH        */
                    _UDWORD :27;                /*              */
                    } BIT;                      /*              */
             } RIICnICBRH;                      /*              */
       union {                                  /* RIICnICDRT   */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD ICDRS:8;            /*   ICDRS      */
                    _UDWORD :24;                /*              */
                    } BIT;                      /*              */
             } RIICnICDRT;                      /*              */
       union {                                  /* RIICnICDRR   */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD ICDRR:8;            /*   ICDRR      */
                    _UDWORD :24;                /*              */
                    } BIT;                      /*              */
             } RIICnICDRR;                      /*              */
};                                              /*              */

#define RIIC_0 (*(volatile struct st_riic_n *)0xFCFEE000)    /* RIIC_0 Address */
#define RIIC_1 (*(volatile struct st_riic_n *)0xFCFEE400)    /* RIIC_1 Address */
#define RIIC_2 (*(volatile struct st_riic_n *)0xFCFEE800)    /* RIIC_2 Address */
#define RIIC_3 (*(volatile struct st_riic_n *)0xFCFEEC00)    /* RIIC_3 Address */


#endif /* __RIIC_IODEFINE_H__ */

/* End of File */
