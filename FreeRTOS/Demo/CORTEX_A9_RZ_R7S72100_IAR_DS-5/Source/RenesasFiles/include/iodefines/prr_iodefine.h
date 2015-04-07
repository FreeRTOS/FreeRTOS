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
* File Name     : prr_iodefine.h
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
*         : 27.07.2012 0.01		参考資料：Aragon_PRR120614.xls	!!!BSIDの内容が仕様書にない!!!
*******************************************************************************/
#ifndef __PRR_IODEFINE_H__
#define __PRR_IODEFINE_H__

#include "typedefine.h"

struct st_prr {                                 /* struct PRR   */
       union {                                  /* MDR          */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD BTMD:3;             /*   BTMD       */
                    _UDWORD :1;                 /*              */
                    _UDWORD BTTEST:1;           /*   BTTEST     */
                    _UDWORD :1;                 /*              */
                    _UDWORD SEC:1;              /*   SEC        */
                    _UDWORD SELFEWP:1;          /*   SELFEWP    */
                    _UDWORD RAMBOOT:1;          /*   RAMBOOT    */
                    _UDWORD :23;                /*              */
                    } BIT;                      /*              */
             } MDR;                             /*              */
       union {                                  /* BSID         */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD dummy:32;                /*              */	/* !!!ビット決定次第、定義する!!! */
                    } BIT;                      /*              */
             } BSID;                            /*              */
       union {                                  /* ECCRR        */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD ECCEN:1;            /*   ECCEN      */
                    _UDWORD :31;                /*              */
                    } BIT;                      /*              */
             } ECCRR;                           /*              */
       _UBYTE wk0[276];                         /*              */
       union {                                  /* SEMRn        */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD SEMF:1;             /*   SEMF       */
                    _UDWORD :31;                /*              */
                    } BIT;                      /*              */
             } SEMRn[32];                       /*              */
       _UBYTE wk1[96];                          /*              */
       union {                                  /* RMPR         */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD AXI64:1;            /*   AXI64      */
                    _UDWORD AXI128:1;           /*   AXI128     */
                    _UDWORD :30;                /*              */
                    } BIT;                      /*              */
             } RMPR;                            /*              */
       union {                                  /* AXIBUSCTL0   */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD ETHAWCACHE:4;       /*   ETHAWCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD ETHARCACHE:4;       /*   ETHARCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD JCUAWCACHE:4;       /*   JCUAWCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD JCUARCACHE:4;       /*   JCUARCACHE */
                    _UDWORD :4;                 /*              */
                    } BIT;                      /*              */
             } AXIBUSCTL0;                      /*              */
       union {                                  /* AXIBUSCTL1   */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD IMR21AWCACHE:4;     /*   IMR21AWCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD IMR21ARCACHE:4;     /*   IMR21ARCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD IMR20AWCACHE:4;     /*   IMR20AWCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD IMR20ARCACHE:4;     /*   IMR20ARCACHE */
                    _UDWORD :4;                 /*              */
                    } BIT;                      /*              */
             } AXIBUSCTL1;                      /*              */
       union {                                  /* AXIBUSCTL2   */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD CEUAWCACHE:4;       /*   CEUAWCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD CEUARCACHE:4;       /*   CEUARCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD IMRDAWCACHE:4;      /*   IMRDAWCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD IMRDARCACHE:4;      /*   IMRDARCACHE */
                    _UDWORD :4;                 /*              */
                    } BIT;                      /*              */
             } AXIBUSCTL2;                      /*              */
       union {                                  /* AXIBUSCTL3   */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD RGP641AWCACHE:4;    /*   RGP641AWCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD RGP641ARCACHE:4;    /*   RGP641ARCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD RGP640AWCACHE:4;    /*   RGP640AWCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD RGP640ARCACHE:4;    /*   RGP640ARCACHE */
                    _UDWORD :4;                 /*              */
                    } BIT;                      /*              */
             } AXIBUSCTL3;                      /*              */
       union {                                  /* AXIBUSCTL4   */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD RGP1280AWCACHE:4;   /*   RGP1280AWCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD RGP1280ARCACHE:4;   /*   RGP1280ARCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD RGP642AWCACHE:4;    /*   RGP642AWCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD RGP642ARCACHE:4;    /*   RGP642ARCACHE */
                    _UDWORD :4;                 /*              */
                    } BIT;                      /*              */
             } AXIBUSCTL4;                      /*              */
       union {                                  /* AXIBUSCTL5   */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD MLB_AxCACHE:2;      /*   MLB_AxCACHE */
                    _UDWORD :14;                /*              */
                    _UDWORD RGP1281AWCACHE:4;   /*   RGP1281AWCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD RGP1281ARCACHE:4;   /*   RGP1281ARCACHE */
                    _UDWORD :4;                 /*              */
                    } BIT;                      /*              */
             } AXIBUSCTL5;                      /*              */
       union {                                  /* AXIBUSCTL6   */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :8;                 /*              */
                    _UDWORD VDC502ARCACHE:4;    /*   VDC502ARCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD VDC501AWCACHE:4;    /*   VDC501AWCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD VDC501ARCACHE:4;    /*   VDC501ARCACHE */
                    _UDWORD :4;                 /*              */
                    } BIT;                      /*              */
             } AXIBUSCTL6;                      /*              */
       union {                                  /* AXIBUSCTL7   */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :8;                 /*              */
                    _UDWORD VDC504ARCACHE:4;    /*   VDC504ARCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD VDC503AWCACHE:4;    /*   VDC503AWCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD VDC503ARCACHE:4;    /*   VDC503ARCACHE */
                    _UDWORD :4;                 /*              */
                    } BIT;                      /*              */
             } AXIBUSCTL7;                      /*              */
       union {                                  /* AXIBUSCTL8   */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD VDC511AWCACHE:4;    /*   VDC511AWCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD VDC511ARCACHE:4;    /*   VDC511ARCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD VDC505AWCACHE:4;    /*   VDC505AWCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD VDC505ARCACHE:4;    /*   VDC505ARCACHE */
                    _UDWORD :4;                 /*              */
                    } BIT;                      /*              */
             } AXIBUSCTL8;                      /*              */
       union {                                  /* AXIBUSCTL9   */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD VDC513AWCACHE:4;    /*   VDC513AWCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD VDC513ARCACHE:4;    /*   VDC513ARCACHE */
                    _UDWORD :12;                /*              */
                    _UDWORD VDC512ARCACHE:4;    /*   VDC512ARCACHE */
                    _UDWORD :4;                 /*              */
                    } BIT;                      /*              */
             } AXIBUSCTL9;                      /*              */
       union {                                  /* AXIBUSCTL10  */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD VDC515AWCACHE:4;    /*   VDC515AWCACHE */
                    _UDWORD :4;                 /*              */
                    _UDWORD VDC515ARCACHE:4;    /*   VDC515ARCACHE */
                    _UDWORD :12;                /*              */
                    _UDWORD VDC514ARCACHE:4;    /*   VDC514ARCACHE */
                    _UDWORD :4;                 /*              */
                    } BIT;                      /*              */
             } AXIBUSCTL10;                     /*              */
       union {                                  /* AXIRERRCTL0  */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :8;                 /*              */
                    _UDWORD CEURERREN:1;        /*   CEURERREN  */
                    _UDWORD :3;                 /*              */
                    _UDWORD IMRDRERREN:1;       /*   IMRDRERREN */
                    _UDWORD :3;                 /*              */
                    _UDWORD IMR21RERREN:1;      /*   IMR21RERREN */
                    _UDWORD :3;                 /*              */
                    _UDWORD IMR20RERREN:1;      /*   IMR20RERREN */
                    _UDWORD :3;                 /*              */
                    _UDWORD ETHRERREN:1;        /*   ETHRERREN  */
                    _UDWORD :3;                 /*              */
                    _UDWORD JCURERREN:1;        /*   JCURERREN  */
                    _UDWORD :3;                 /*              */
                    } BIT;                      /*              */
             } AXIRERRCTL0;                     /*              */
       union {                                  /* AXIRERRCTL1  */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :12;                /*              */
                    _UDWORD RGP1281RERREN:1;    /*   RGP1281RERREN */
                    _UDWORD :3;                 /*              */
                    _UDWORD RGP1280RERREN:1;    /*   RGP1280RERREN */
                    _UDWORD :3;                 /*              */
                    _UDWORD RGP642RERREN:1;     /*   RGP642RERREN */
                    _UDWORD :3;                 /*              */
                    _UDWORD RGP641RERREN:1;     /*   RGP641RERREN */
                    _UDWORD :3;                 /*              */
                    _UDWORD RGP640RERREN:1;     /*   RGP640RERREN */
                    _UDWORD :3;                 /*              */
                    } BIT;                      /*              */
             } AXIRERRCTL1;                     /*              */
       union {                                  /* AXIRERRCTL2  */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :12;                /*              */
                    _UDWORD VDC505RERREN:1;     /*   VDC505RERREN */
                    _UDWORD :3;                 /*              */
                    _UDWORD VDC504RERREN:1;     /*   VDC504RERREN */
                    _UDWORD :3;                 /*              */
                    _UDWORD VDC503RERREN:1;     /*   VDC503RERREN */
                    _UDWORD :3;                 /*              */
                    _UDWORD VDC502RERREN:1;     /*   VDC502RERREN */
                    _UDWORD :3;                 /*              */
                    _UDWORD VDC501RERREN:1;     /*   VDC501RERREN */
                    _UDWORD :3;                 /*              */
                    } BIT;                      /*              */
             } AXIRERRCTL2;                     /*              */
       union {                                  /* AXIRERRCTL3  */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :12;                /*              */
                    _UDWORD VDC515RERREN:1;     /*   VDC515RERREN */
                    _UDWORD :3;                 /*              */
                    _UDWORD VDC514RERREN:1;     /*   VDC514RERREN */
                    _UDWORD :3;                 /*              */
                    _UDWORD VDC513RERREN:1;     /*   VDC513RERREN */
                    _UDWORD :3;                 /*              */
                    _UDWORD VDC512RERREN:1;     /*   VDC512RERREN */
                    _UDWORD :3;                 /*              */
                    _UDWORD VDC511RERREN:1;     /*   VDC511RERREN */
                    _UDWORD :3;                 /*              */
                    } BIT;                      /*              */
             } AXIRERRCTL3;                     /*              */
       union {                                  /* AXIRERRST0   */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :8;                 /*              */
                    _UDWORD CEUBRESP:2;         /*   CEUBRESP   */
                    _UDWORD CEURRESP:2;         /*   CEURRESP   */
                    _UDWORD IMRDBRESP:2;        /*   IMRDBRESP  */
                    _UDWORD IMRDRRESP:2;        /*   IMRDRRESP  */
                    _UDWORD IMR21BRESP:2;       /*   IMR21BRESP */
                    _UDWORD IMR21RRESP:2;       /*   IMR21RRESP */
                    _UDWORD IMR20BRESP:2;       /*   IMR20BRESP */
                    _UDWORD IMR20RRESP:2;       /*   IMR20RRESP */
                    _UDWORD ETHBRESP:2;         /*   ETHBRESP   */
                    _UDWORD ETHRRESP:2;         /*   ETHRRESP   */
                    _UDWORD JCUBRESP:2;         /*   JCUBRESP   */
                    _UDWORD JCURRESP:2;         /*   JCURRESP   */
                    } BIT;                      /*              */
             } AXIRERRST0;                      /*              */
       union {                                  /* AXIRERRST1   */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :12;                /*              */
                    _UDWORD RGP1281BRESP:2;     /*   RGP1281BRESP */
                    _UDWORD RGP1281RRESP:2;     /*   RGP1281RRESP */
                    _UDWORD RGP1280BRESP:2;     /*   RGP1280BRESP */
                    _UDWORD RGP1280RRESP:2;     /*   RGP1280RRESP */
                    _UDWORD RGP642BRESP:2;      /*   RGP642BRESP */
                    _UDWORD RGP642RRESP:2;      /*   RGP642RRESP */
                    _UDWORD RGP641BRESP:2;      /*   RGP641BRESP */
                    _UDWORD RGP641RRESP:2;      /*   RGP641RRESP */
                    _UDWORD RGP640BRESP:2;      /*   RGP640BRESP */
                    _UDWORD RGP640RRESP:2;      /*   RGP640RRESP */
                    } BIT;                      /*              */
             } AXIRERRST1;                      /*              */
       union {                                  /* AXIRERRST2   */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :12;                /*              */
                    _UDWORD VDC505BRESP:2;      /*   VDC505BRESP */
                    _UDWORD VDC505RRESP:2;      /*   VDC505RRESP */
                    _UDWORD VDC504BRESP:2;      /*   VDC504BRESP */
                    _UDWORD VDC504RRESP:2;      /*   VDC504RRESP */
                    _UDWORD VDC503BRESP:2;      /*   VDC503BRESP */
                    _UDWORD VDC503RRESP:2;      /*   VDC503RRESP */
                    _UDWORD VDC502BRESP:2;      /*   VDC502BRESP */
                    _UDWORD VDC502RRESP:2;      /*   VDC502RRESP */
                    _UDWORD VDC501BRESP:2;      /*   VDC501BRESP */
                    _UDWORD VDC501RRESP:2;      /*   VDC501RRESP */
                    } BIT;                      /*              */
             } AXIRERRST2;                      /*              */
       union {                                  /* AXIRERRST3   */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :12;                /*              */
                    _UDWORD VDC515BRESP:2;      /*   VDC515BRESP */
                    _UDWORD VDC515RRESP:2;      /*   VDC515RRESP */
                    _UDWORD VDC514BRESP:2;      /*   VDC514BRESP */
                    _UDWORD VDC514RRESP:2;      /*   VDC514RRESP */
                    _UDWORD VDC513BRESP:2;      /*   VDC513BRESP */
                    _UDWORD VDC513RRESP:2;      /*   VDC513RRESP */
                    _UDWORD VDC512BRESP:2;      /*   VDC512BRESP */
                    _UDWORD VDC512RRESP:2;      /*   VDC512RRESP */
                    _UDWORD VDC511BRESP:2;      /*   VDC511BRESP */
                    _UDWORD VDC511RRESP:2;      /*   VDC511RRESP */
                    } BIT;                      /*              */
             } AXIRERRST3;                      /*              */
       union {                                  /* AXIRERRCLR0  */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :8;                 /*              */
                    _UDWORD CEUBRESPCLR:1;      /*   CEUBRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD CEURRESPCLR:1;      /*   CEURRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD IMRDBRESPCLR:1;     /*   IMRDBRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD IMRDRRESPCLR:1;     /*   IMRDRRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD IMR21BRESPCLR:1;    /*   IMR21BRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD IMR21RRESPCLR:1;    /*   IMR21RRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD IMR20BRESPCLR:1;    /*   IMR20BRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD IMR20RRESPCLR:1;    /*   IMR20RRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD ETHBRESPCLR:1;      /*   ETHBRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD ETHRRESPCLR:1;      /*   ETHRRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD JCUBRESPCLR:1;      /*   JCUBRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD JCURRESPCLR:1;      /*   JCURRESPCLR */
                    _UDWORD :1;                 /*              */
                    } BIT;                      /*              */
             } AXIRERRCLR0;                     /*              */
       union {                                  /* AXIRERRCLR1  */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :12;                /*              */
                    _UDWORD RGP1281BRESPCLR:1;  /*   RGP1281BRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD RGP1281RRESPCLR:1;  /*   RGP1281RRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD RGP1280BRESPCLR:1;  /*   RGP1280BRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD RGP1280RRESPCLR:1;  /*   RGP1280RRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD RGP642BRESPCLR:1;   /*   RGP642BRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD RGP642RRESPCLR:1;   /*   RGP642RRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD RGP641BRESPCLR:1;   /*   RGP641BRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD RGP641RRESPCLR:1;   /*   RGP641RRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD RGP640BRESPCLR:1;   /*   RGP640BRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD RGP640RRESPCLR:1;   /*   RGP640RRESPCLR */
                    _UDWORD :1;                 /*              */
                    } BIT;                      /*              */
             } AXIRERRCLR1;                     /*              */
       union {                                  /* AXIRERRCLR2  */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :12;                /*              */
                    _UDWORD VDC505BRESPCLR:1;   /*   VDC505BRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD VDC505RRESPCLR:1;   /*   VDC505RRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD VDC504BRESPCLR:1;   /*   VDC504BRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD VDC504RRESPCLR:1;   /*   VDC504RRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD VDC503BRESPCLR:1;   /*   VDC503BRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD VDC503RRESPCLR:1;   /*   VDC503RRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD VDC502BRESPCLR:1;   /*   VDC502BRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD VDC502RRESPCLR:1;   /*   VDC502RRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD VDC501BRESPCLR:1;   /*   VDC501BRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD VDC501RRESPCLR:1;   /*   VDC501RRESPCLR */
                    _UDWORD :1;                 /*              */
                    } BIT;                      /*              */
             } AXIRERRCLR2;                     /*              */
       union {                                  /* AXIRERRCLR3  */
       _UDWORD LONG;                            /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD :12;                /*              */
                    _UDWORD VDC515BRESPCLR:1;   /*   VDC515BRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD VDC515RRESPCLR:1;   /*   VDC515RRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD VDC514BRESPCLR:1;   /*   VDC514BRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD VDC514RRESPCLR:1;   /*   VDC514RRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD VDC513BRESPCLR:1;   /*   VDC513BRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD VDC513RRESPCLR:1;   /*   VDC513RRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD VDC512BRESPCLR:1;   /*   VDC512BRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD VDC512RRESPCLR:1;   /*   VDC512RRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD VDC511BRESPCLR:1;   /*   VDC511BRESPCLR */
                    _UDWORD :1;                 /*              */
                    _UDWORD VDC511RRESPCLR:1;   /*   VDC511RRESPCLR */
                    _UDWORD :1;                 /*              */
                    } BIT;                      /*              */
             } AXIRERRCLR3;                     /*              */
};                                              /*              */

#define	PRR		(*(volatile struct st_prr *)0xFCFE1800)   /* PRR Address */


#endif /* __PRR_IODEFINE_H__ */

/* End of File */
