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
*   File Name   : mtu2_iodefine.h
*   Abstract    : 
*   Version     : 1.00.00
*   Device      : ARM
*   Tool-Chain  : 
*   OS          : None
*   H/W Platform: 
*   Description : 
********************************************************************************
*   History     : Jan.11,2013 Ver.1.00.00
*******************************************************************************/
#ifndef __MTU2_IODEFINE_H__
#define __MTU2_IODEFINE_H__

#include "typedefine.h"

struct st_mtu2{                                 /* struct MTU2  */
       union {                                  /* TCR_2        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TPSC:3;              /*   TPSC       */
                    _UBYTE CKEG:2;              /*   CKEG       */
                    _UBYTE CCLR:2;              /*   CCLR       */
                    _UBYTE :1;
                    } BIT;                      /*              */
             } TCR_2;                           /*              */
       union {                                  /* TMDR_2       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MD:4;                /*   MD         */
                    _UBYTE :4;                  /*              */
                    } BIT;                      /*              */
             } TMDR_2;                          /*              */
       union {                                  /* TIOR_2       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE IOA:4;               /*   IOA        */
                    _UBYTE IOB:4;               /*   IOB        */
                    } BIT;                      /*              */
             } TIOR_2;                          /*              */
       _UBYTE wk0[1];                           /*              */
       union {                                  /* TIER_2       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TGIEA:1;             /*   TGIEA      */
                    _UBYTE TGIEB:1;             /*   TGIEB      */
                    _UBYTE :2;                  /*              */
                    _UBYTE TCIEV:1;             /*   TCIEV      */
                    _UBYTE TCIEU:1;             /*   TCIEU      */
                    _UBYTE :1;                  /*              */
                    _UBYTE TTGE:1;              /*   TTGE       */
                    } BIT;                      /*              */
             } TIER_2;                          /*              */
       union {                                  /* TSR_2        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TGFA:1;              /*   TGFA       */
                    _UBYTE TGFB:1;              /*   TGFB       */
                    _UBYTE :1;                  /*              */
                    _UBYTE :1;                  /*             */
                    _UBYTE TCFV:1;              /*   TCFV       */
                    _UBYTE TCFU:1;              /*   TCFU       */
                    _UBYTE :1;                  /*              */
                    _UBYTE TCFD:1;              /*   TCFD       */
                    } BIT;                      /*              */
             } TSR_2;                           /*              */
       union {                                  /* TCNT_2       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TCNT_2;                          /*              */
       union {                                  /* TGRA_2       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRA_2;                          /*              */
       union {                                  /* TGRB_2       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRB_2;                          /*              */
       _UBYTE wk1[500];                         /*              */
       union {                                  /* TCR_3        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TPSC:3;              /*   TPSC       */
                    _UBYTE CKEG:2;              /*   CKEG       */
                    _UBYTE CCLR:3;              /*   CCLR       */
                    } BIT;                      /*              */
             } TCR_3;                           /*              */
       union {                                  /* TCR_4        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TPSC:3;              /*   TPSC       */
                    _UBYTE CKEG:2;              /*   CKEG       */
                    _UBYTE CCLR:3;              /*   CCLR       */
                    } BIT;                      /*              */
             } TCR_4;                           /*              */
       union {                                  /* TMDR_3       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MD:4;                /*   MD         */
                    _UBYTE BFA:1;               /*   BFA        */
                    _UBYTE BFB:1;               /*   BFB        */
                    _UBYTE :2;                  /*              */
                    } BIT;                      /*              */
             } TMDR_3;                          /*              */
       union {                                  /* TMDR_4       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MD:4;                /*   MD         */
                    _UBYTE BFA:1;               /*   BFA        */
                    _UBYTE BFB:1;               /*   BFB        */
                    _UBYTE :2;                  /*              */
                    } BIT;                      /*              */
             } TMDR_4;                          /*              */
       union {                                  /* TIORH_3      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE IOA:4;               /*   IOA        */
                    _UBYTE IOB:4;               /*   IOB        */
                    } BIT;                      /*              */
             } TIORH_3;                         /*              */
       union {                                  /* TIORL_3      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE IOC:4;               /*   IOC        */
                    _UBYTE IOD:4;               /*   IOD        */
                    } BIT;                      /*              */
             } TIORL_3;                         /*              */
       union {                                  /* TIORH_4      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE IOA:4;               /*   IOA        */
                    _UBYTE IOB:4;               /*   IOB        */
                    } BIT;                      /*              */
             } TIORH_4;                         /*              */
       union {                                  /* TIORL_4      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE IOC:4;               /*   IOC        */
                    _UBYTE IOD:4;               /*   IOD        */
                    } BIT;                      /*              */
             } TIORL_4;                         /*              */
       union {                                  /* TIER_3       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TGIEA:1;             /*   TGIEA      */
                    _UBYTE TGIEB:1;             /*   TGIEB      */
                    _UBYTE TGIEC:1;             /*   TGIEC      */
                    _UBYTE TGIED:1;             /*   TGIED      */
                    _UBYTE TCIEV:1;             /*   TCIEV      */
                    _UBYTE :2;                  /*              */
                    _UBYTE TTGE:1;              /*   TTGE       */
                    } BIT;                      /*              */
             } TIER_3;                          /*              */
       union {                                  /* TIER_4       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TGIEA:1;             /*   TGIEA      */
                    _UBYTE TGIEB:1;             /*   TGIEB      */
                    _UBYTE TGIEC:1;             /*   TGIEC      */
                    _UBYTE TGIED:1;             /*   TGIED      */
                    _UBYTE TCIEV:1;             /*   TCIEV      */
                    _UBYTE :1;                  /*              */
                    _UBYTE TTGE2:1;             /*   TTGE2      */
                    _UBYTE TTGE:1;              /*   TTGE       */
                    } BIT;                      /*              */
             } TIER_4;                          /*              */
       union {                                  /* TOER         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE OE3B:1;              /*   OE3B       */
                    _UBYTE OE4A:1;              /*   OE4A       */
                    _UBYTE OE4B:1;              /*   OE4B       */
                    _UBYTE OE3D:1;              /*   OE3D       */
                    _UBYTE OE4C:1;              /*   OE4C       */
                    _UBYTE OE4D:1;              /*   OE4D       */
                    _UBYTE :2;                  /*              */
                    } BIT;                      /*              */
             } TOER;                            /*              */
       _UBYTE wk2[2];                           /*              */
       union {                                  /* TGCR         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE UF:1;                /*   UF         */
                    _UBYTE VF:1;                /*   VF         */
                    _UBYTE WF:1;                /*   WF         */
                    _UBYTE FB:1;                /*   FB         */
                    _UBYTE P:1;                 /*   P          */
                    _UBYTE N:1;                 /*   N          */
                    _UBYTE BDC:1;               /*   BDC        */
                    _UBYTE :1;                  /*              */
                    } BIT;                      /*              */
             } TGCR;                            /*              */
       union {                                  /* TOCR1        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE OLSP:1;              /*   OLSP       */
                    _UBYTE OLSN:1;              /*   OLSN       */
                    _UBYTE TOCS:1;              /*   TOCS       */
                    _UBYTE TOCL:1;              /*   TOCL       */
                    _UBYTE :2;                  /*              */
                    _UBYTE PSYE:1;              /*   PSYE       */
                    _UBYTE :1;                  /*              */
                    } BIT;                      /*              */
             } TOCR1;                           /*              */
       union {                                  /* TOCR2        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE OLS1P:1;             /*   OLS1P      */
                    _UBYTE OLS1N:1;             /*   OLS1N      */
                    _UBYTE OLS2P:1;             /*   OLS2P      */
                    _UBYTE OLS2N:1;             /*   OLS2N      */
                    _UBYTE OLS3P:1;             /*   OLS3P      */
                    _UBYTE OLS3N:1;             /*   OLS3N      */
                    _UBYTE BF:2;                /*   BF         */
                    } BIT;                      /*              */
             } TOCR2;                           /*              */
       union {                                  /* TCNT_3       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TCNT_3;                          /*              */
       union {                                  /* TCNT_4       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TCNT_4;                          /*              */
       union {                                  /* TCDR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TCDR;                            /*              */
       union {                                  /* TDDR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TDDR;                            /*              */
       union {                                  /* TGRA_3       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRA_3;                          /*              */
       union {                                  /* TGRB_3       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRB_3;                          /*              */
       union {                                  /* TGRA_4       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRA_4;                          /*              */
       union {                                  /* TGRB_4       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRB_4;                          /*              */
       union {                                  /* TCNTS        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TCNTS;                           /*              */
       union {                                  /* TCBR         */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TCBR;                            /*              */
       union {                                  /* TGRC_3       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRC_3;                          /*              */
       union {                                  /* TGRD_3       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRD_3;                          /*              */
       union {                                  /* TGRC_4       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRC_4;                          /*              */
       union {                                  /* TGRD_4       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRD_4;                          /*              */
       union {                                  /* TSR_3        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TGFA:1;              /*   TGFA       */
                    _UBYTE TGFB:1;              /*   TGFB       */
                    _UBYTE TGFC:1;              /*   TGFC       */
                    _UBYTE TGFD:1;              /*   TGFD       */
                    _UBYTE TCFV:1;              /*   TCFV       */
                    _UBYTE :2;                  /*              */
                    _UBYTE TCFD:1;              /*   TCFD       */
                    } BIT;                      /*              */
             } TSR_3;                           /*              */
       union {                                  /* TSR_4        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TGFA:1;              /*   TGFA       */
                    _UBYTE TGFB:1;              /*   TGFB       */
                    _UBYTE TGFC:1;              /*   TGFC       */
                    _UBYTE TGFD:1;              /*   TGFD       */
                    _UBYTE TCFV:1;              /*   TCFV       */
                    _UBYTE :2;                  /*              */
                    _UBYTE TCFD:1;              /*   TCFD       */
                    } BIT;                      /*              */
             } TSR_4;                           /*              */
       _UBYTE wk3[2];                           /*              */
       union {                                  /* TITCR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE _4VCOR:3;            /*   _4VCOR     */
                    _UBYTE T4VEN:1;             /*   T4VEN      */
                    _UBYTE _3ACOR:3;            /*   _3ACOR     */
                    _UBYTE T3AEN:1;             /*   T3AEN      */
                    } BIT;                      /*              */
             } TITCR;                           /*              */
       union {                                  /* TITCNT       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE _4VCNT:3;            /*   _4VCNT     */
                    _UBYTE :1;                  /*              */
                    _UBYTE _3ACNT:3;            /*   _3ACNT     */
                    _UBYTE :1;                  /*              */
                    } BIT;                      /*              */
             } TITCNT;                          /*              */
       union {                                  /* TBTER        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE BTE:2;               /*   BTE        */
                    _UBYTE :6;                  /*              */
                    } BIT;                      /*              */
             } TBTER;                           /*              */
       _UBYTE wk4[1];                           /*              */
       union {                                  /* TDER         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TDER:1;              /*   TDER       */
                    _UBYTE :7;                  /*              */
                    } BIT;                      /*              */
             } TDER;                            /*              */
       _UBYTE wk5[1];                           /*              */
       union {                                  /* TOLBR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE OLS1P:1;             /*   OLS1P      */
                    _UBYTE OLS1N:1;             /*   OLS1N      */
                    _UBYTE OLS2P:1;             /*   OLS2P      */
                    _UBYTE OLS2N:1;             /*   OLS2N      */
                    _UBYTE OLS3P:1;             /*   OLS3P      */
                    _UBYTE OLS3N:1;             /*   OLS3N      */
                    _UBYTE :2;                  /*              */
                    } BIT;                      /*              */
             } TOLBR;                           /*              */
       _UBYTE wk6[1];                           /*              */
       union {                                  /* TBTM_3       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TTSA:1;              /*   TTSA       */
                    _UBYTE TTSB:1;              /*   TTSB       */
                    _UBYTE :6;                  /*              */
                    } BIT;                      /*              */
             } TBTM_3;                          /*              */
       union {                                  /* TBTM_4       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TTSA:1;              /*   TTSA       */
                    _UBYTE TTSB:1;              /*   TTSB       */
                    _UBYTE :6;                  /*              */
                    } BIT;                      /*              */
             } TBTM_4;                          /*              */
       _UBYTE wk7[6];                           /*              */
       union {                                  /* TADCR        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD ITB4VE:1;            /*   ITB4VE     */
                    _UWORD ITB3AE:1;            /*   ITB3AE     */
                    _UWORD ITA4VE:1;            /*   ITA4VE     */
                    _UWORD ITA3AE:1;            /*   ITA3AE     */
                    _UWORD DT4BE:1;             /*   DT4BE      */
                    _UWORD UT4BE:1;             /*   UT4BE      */
                    _UWORD DT4AE:1;             /*   DT4AE      */
                    _UWORD UT4AE:1;             /*   UT4AE      */
                    _UWORD :6;                  /*              */
                    _UWORD BF:2;                /*   BF         */
                    } BIT;                      /*              */
             } TADCR;                           /*              */
       _UBYTE wk8[2];                           /*              */
       union {                                  /* TADCORA_4    */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TADCORA_4;                       /*              */
       union {                                  /* TADCORB_4    */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TADCORB_4;                       /*              */
       union {                                  /* TADCOBRA_4   */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TADCOBRA_4;                      /*              */
       union {                                  /* TADCOBRB_4   */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TADCOBRB_4;                      /*              */
       _UBYTE wk9[20];                          /*              */
       union {                                  /* TWCR         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE WRE:1;               /*   WRE        */
                    _UBYTE :6;                  /*              */
                    _UBYTE CCE:1;               /*   CCE        */
                    } BIT;                      /*              */
             } TWCR;                            /*              */
       _UBYTE wk10[31];                         /*              */
       union {                                  /* TSTR         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE CST0:1;              /*   CST0       */
                    _UBYTE CST1:1;              /*   CST1       */
                    _UBYTE CST2:1;              /*   CST2       */
                    _UBYTE :3;                  /*              */
                    _UBYTE CST3:1;              /*   CST3       */
                    _UBYTE CST4:1;              /*   CST4       */
                    } BIT;                      /*              */
             } TSTR;                            /*              */
       union {                                  /* TSYR         */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE SYNC0:1;             /*   SYNC0      */
                    _UBYTE SYNC1:1;             /*   SYNC1      */
                    _UBYTE SYNC2:1;             /*   SYNC2      */
                    _UBYTE :3;                  /*              */
                    _UBYTE SYNC3:1;             /*   SYNC3      */
                    _UBYTE SYNC4:1;             /*   SYNC4      */
                    } BIT;                      /*              */
             } TSYR;                            /*              */
       _UBYTE wk11[2];                          /*              */
       union {                                  /* TRWER        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE RWE:1;               /*   RWE        */
                    _UBYTE :7;                  /*              */
                    } BIT;                      /*              */
             } TRWER;                           /*              */
       _UBYTE wk12[123];                        /*              */
       union {                                  /* TCR_0        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TPSC:3;              /*   TPSC       */
                    _UBYTE CKEG:2;              /*   CKEG       */
                    _UBYTE CCLR:3;              /*   CCLR       */
                    } BIT;                      /*              */
             } TCR_0;                           /*              */
       union {                                  /* TMDR_0       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MD:4;                /*   MD         */
                    _UBYTE BFA:1;               /*   BFA        */
                    _UBYTE BFB:1;               /*   BFB        */
                    _UBYTE BFE:1;               /*   BFE        */
                    _UBYTE :1;                  /*              */
                    } BIT;                      /*              */
             } TMDR_0;                          /*              */
       union {                                  /* TIORH_0      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE IOA:4;               /*   IOA        */
                    _UBYTE IOB:4;               /*   IOB        */
                    } BIT;                      /*              */
             } TIORH_0;                         /*              */
       union {                                  /* TIORL_0      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE IOC:4;               /*   IOC        */
                    _UBYTE IOD:4;               /*   IOD        */
                    } BIT;                      /*              */
             } TIORL_0;                         /*              */
       union {                                  /* TIER_0       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TGIEA:1;             /*   TGIEA      */
                    _UBYTE TGIEB:1;             /*   TGIEB      */
                    _UBYTE TGIEC:1;             /*   TGIEC      */
                    _UBYTE TGIED:1;             /*   TGIED      */
                    _UBYTE TCIEV:1;             /*   TCIEV      */
                    _UBYTE :2;                  /*              */
                    _UBYTE TTGE:1;              /*   TTGE       */
                    } BIT;                      /*              */
             } TIER_0;                          /*              */
       union {                                  /* TSR_0        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TGFA:1;              /*   TGFA       */
                    _UBYTE TGFB:1;              /*   TGFB       */
                    _UBYTE TGFC:1;              /*   TGFC       */
                    _UBYTE TGFD:1;              /*   TGFD       */
                    _UBYTE TCFV:1;              /*   TCFV       */
                    _UBYTE :3;                  /*              */
                    } BIT;                      /*              */
             } TSR_0;                           /*              */
       union {                                  /* TCNT_0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TCNT_0;                          /*              */
       union {                                  /* TGRA_0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRA_0;                          /*              */
       union {                                  /* TGRB_0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRB_0;                          /*              */
       union {                                  /* TGRC_0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRC_0;                          /*              */
       union {                                  /* TGRD_0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRD_0;                          /*              */
       _UBYTE wk13[16];                         /*              */
       union {                                  /* TGRE_0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRE_0;                          /*              */
       union {                                  /* TGRF_0       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRF_0;                          /*              */
       union {                                  /* TIER2_0      */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TGIEE:1;             /*   TGIEE      */
                    _UBYTE TGIEF:1;             /*   TGIEF      */
                    _UBYTE :5;                  /*              */
                    _UBYTE TTGE2:1;             /*   TTGE2      */
                    } BIT;                      /*              */
             } TIER2_0;                         /*              */
       union {                                  /* TSR2_0       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TGFE:1;              /*   TGFE       */
                    _UBYTE TGFF:1;              /*   TGFF       */
                    _UBYTE :6;                  /*              */
                    } BIT;                      /*              */
             } TSR2_0;                          /*              */
       union {                                  /* TBTM_0       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TTSA:1;              /*   TTSA       */
                    _UBYTE TTSB:1;              /*   TTSB       */
                    _UBYTE TTSE:1;              /*   TTSE       */
                    _UBYTE :5;                  /*              */
                    } BIT;                      /*              */
             } TBTM_0;                          /*              */
       _UBYTE wk14[89];                         /*              */
       union {                                  /* TCR_1        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TPSC:3;              /*   TPSC       */
                    _UBYTE CKEG:2;              /*   CKEG       */
                    _UBYTE CCLR:2;              /*   CCLR       */
                    _UBYTE :1;
                    } BIT;                      /*              */
             } TCR_1;                           /*              */
       union {                                  /* TMDR_1       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE MD:4;                /*   MD         */
                    _UBYTE :4;                  /*              */
                    } BIT;                      /*              */
             } TMDR_1;                          /*              */
       union {                                  /* TIOR_1       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE IOA:4;               /*   IOA        */
                    _UBYTE IOB:4;               /*   IOB        */
                    } BIT;                      /*              */
             } TIOR_1;                          /*              */
       _UBYTE wk15[1];                          /*              */
       union {                                  /* TIER_1       */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TGIEA:1;             /*   TGIEA      */
                    _UBYTE TGIEB:1;             /*   TGIEB      */
                    _UBYTE :2;                  /*              */
                    _UBYTE TCIEV:1;             /*   TCIEV      */
                    _UBYTE TCIEU:1;             /*   TCIEU      */
                    _UBYTE :1;                  /*              */
                    _UBYTE TTGE:1;              /*   TTGE       */
                    } BIT;                      /*              */
             } TIER_1;                          /*              */
       union {                                  /* TSR_1        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE TGFA:1;              /*   TGFA       */
                    _UBYTE TGFB:1;              /*   TGFB       */
                    _UBYTE :2;                  /*              */
                    _UBYTE TCFV:1;              /*   TCFV       */
                    _UBYTE TCFU:1;              /*   TCFU       */
                    _UBYTE :1;                  /*              */
                    _UBYTE TCFD:1;              /*   TCFD       */
                    } BIT;                      /*              */
             } TSR_1;                           /*              */
       union {                                  /* TCNT_1       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TCNT_1;                          /*              */
       union {                                  /* TGRA_1       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRA_1;                          /*              */
       union {                                  /* TGRB_1       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD D:16;                /*   D          */
                    } BIT;                      /*              */
             } TGRB_1;                          /*              */
       _UBYTE wk16[4];                          /*              */
       union {                                  /* TICCR        */
             _UBYTE BYTE;                       /*  Byte Access */
             struct {                           /*  Bit Access  */
                    _UBYTE I1AE:1;              /*   I1AE       */
                    _UBYTE I1BE:1;              /*   I1BE       */
                    _UBYTE I2AE:1;              /*   I2AE       */
                    _UBYTE I2BE:1;              /*   I2BE       */
                    _UBYTE :4;                  /*              */
                    } BIT;                      /*              */
             } TICCR;                           /*              */
};                                              /*              */


#define MTU2 (*(volatile struct st_mtu2 *)0xFCFF0000)  /* MTU2 Address */

#endif /* __MTU2_IODEFINE_H__ */
/* End of File */
