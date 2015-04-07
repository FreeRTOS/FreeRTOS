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
*   File Name   : dmac_iodefine.h
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
#ifndef __DMAC_IODEFINE_H__
#define __DMAC_IODEFINE_H__

#include "typedefine.h"

struct st_dmac_n {                              /* struct DMAC  */
       union {                                  /* N0SA         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD SA:32;              /*   SA         */
                    } BIT;                      /*              */
             } N0SA;                            /*              */
       union {                                  /* N0DA         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD DA:32;              /*   DA         */
                    } BIT;                      /*              */
             } N0DA;                            /*              */
       union {                                  /* N0TB         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD TB:32;              /*   TB         */
                    } BIT;                      /*              */
             } N0TB;                            /*              */
       union {                                  /* N1SA         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD SA:32;              /*   SA         */
                    } BIT;                      /*              */
             } N1SA;                            /*              */
       union {                                  /* N1DA         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD DA:32;              /*   DA         */
                    } BIT;                      /*              */
             } N1DA;                            /*              */
       union {                                  /* N1TB         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD TB:32;              /*   TB         */
                    } BIT;                      /*              */
             } N1TB;                            /*              */
       union {                                  /* CRSA         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD CRSA:32;            /*   CRSA       */
                    } BIT;                      /*              */
             } CRSA;                            /*              */
       union {                                  /* CRDA         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD CRDA:32;            /*   CRDA       */
                    } BIT;                      /*              */
             } CRDA;                            /*              */
       union {                                  /* CRTB         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD CRTB:32;            /*   CRTB       */
                    } BIT;                      /*              */
             } CRTB;                            /*              */
       union {                                  /* CHSTAT       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD EN:1;               /*   EN         */
                    _UDWORD RQST:1;             /*   RQST       */
                    _UDWORD TACT:1;             /*   TACT       */
                    _UDWORD SUS:1;              /*   SUS        */
                    _UDWORD ER:1;               /*   ER         */
                    _UDWORD END:1;              /*   END        */
                    _UDWORD TC:1;               /*   TC         */
                    _UDWORD SR:1;               /*   SR         */
                    _UDWORD DL:1;               /*   DL         */
                    _UDWORD DW:1;               /*   DW         */
                    _UDWORD DER:1;              /*   DER        */
                    _UDWORD MODE:1;             /*   MODE       */
                    _UWORD :4;                  /*              */
                    _UDWORD INTMSK:1;           /*   INTMSK     */
                    _UWORD :15;                 /*              */
                    } BIT;                      /*              */
             } CHSTAT;                          /*              */
       union {                                  /* CHCTRL       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD SETEN:1;            /*   SETEN      */
                    _UDWORD CLREN:1;            /*   CLREN      */
                    _UDWORD STG:1;              /*   STG        */
                    _UDWORD SWRST:1;            /*   SWRST      */
                    _UDWORD CLRRQ:1;            /*   CLRRQ      */
                    _UDWORD CLREND:1;           /*   CLREND     */
                    _UDWORD CLRTC:1;            /*   CLRTC      */
                    _UWORD :1;                  /*              */
                    _UDWORD SETSUS:1;           /*   SETSUS     */
                    _UDWORD CLRSUS:1;           /*   CLRSUS     */
                    _UWORD :6;                  /*              */
                    _UDWORD SETINTMSK:1;        /*   SETINTMSK  */
                    _UDWORD CLRINTMSK:1;        /*   CLRINTMSK  */
                    _UWORD :14;                 /*              */
                    } BIT;                      /*              */
             } CHCTRL;                          /*              */
       union {                                  /* CHCFG        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD SEL:3;              /*   SEL        */
                    _UDWORD REQD:1;             /*   REQD       */
                    _UDWORD LOEN:1;             /*   LOEN       */
                    _UDWORD HIEN:1;             /*   HIEN       */
                    _UDWORD LVL:1;              /*   LVL        */
                    _UWORD :1;                  /*              */
                    _UDWORD AM:3;               /*   AM         */
                    _UWORD :1;                  /*              */
                    _UDWORD SDS:4;              /*   SDS        */
                    _UDWORD DDS:4;              /*   DDS        */
                    _UDWORD SAD:1;              /*   SAD        */
                    _UDWORD DAD:1;              /*   DAD        */
                    _UDWORD TM:1;               /*   TM         */
                    _UWORD :1;                  /*              */
                    _UDWORD DEM:1;              /*   DEM        */
                    _UDWORD TCM:1;              /*   TCM        */
                    _UWORD :1;                  /*              */
                    _UDWORD SBE:1;              /*   SBE        */
                    _UDWORD RSEL:1;             /*   RSEL       */
                    _UDWORD RSW:1;              /*   RSW        */
                    _UDWORD REN:1;              /*   REN        */
                    _UDWORD DMS:1;              /*   DMS        */
                    } BIT;                      /*              */
             } CHCFG;                           /*              */
       union {                                  /* CHITVL       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD ITVL:16;            /*   ITVL       */
                    _UWORD :16;                 /*              */
                    } BIT;                      /*              */
             } CHITVL;                          /*              */
       union {                                  /* CHEXT        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UWORD :4;                  /*              */
                    _UDWORD SCA:4;              /*   SCA        */
                    _UWORD :4;                  /*              */
                    _UDWORD DCA:4;              /*   DCA        */
                    _UWORD :16;                 /*              */
                    } CHEXT;                    /*              */
             } CHEXT;                           /*              */
       union {                                  /* NXLA         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD NXLA:32;            /*   NXLA       */
                    } BIT;                      /*              */
             } NXLA;                            /*              */
       union {                                  /* CRLA         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD CRLA:32;            /*   CRLA       */
                    } BIT;                      /*              */
             } CRLA;                            /*              */
};                                              /*              */

struct st_dmac_07 {                             /* struct DMAC  */
       union {                                  /* DCTRL        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD PR:1;               /*   PR         */
                    _UDWORD LVINT:1;            /*   LVINT      */
                    _UWORD :18;                 /*              */
                    _UDWORD LDCA:4;             /*   LDCA       */
                    _UWORD :4;                  /*              */
                    _UDWORD LWCA:4;             /*   LWCA       */
                    } BIT;                      /*              */
             } DCTRL;                           /*              */
       union {                                  /* DSTAT_EN     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD EN0:1;              /*   EN0        */
                    _UDWORD EN1:1;              /*   EN1        */
                    _UDWORD EN2:1;              /*   EN2        */
                    _UDWORD EN3:1;              /*   EN3        */
                    _UDWORD EN4:1;              /*   EN4        */
                    _UDWORD EN5:1;              /*   EN5        */
                    _UDWORD EN6:1;              /*   EN6        */
                    _UDWORD EN7:1;              /*   EN7        */
                    _UWORD :24;                 /*              */
                    } BIT;                      /*              */
             } DSTAT_EN;                        /*              */
       union {                                  /* DSTAT_ER     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD ER0:1;              /*   ER0        */
                    _UDWORD ER1:1;              /*   ER1        */
                    _UDWORD ER2:1;              /*   ER2        */
                    _UDWORD ER3:1;              /*   ER3        */
                    _UDWORD ER4:1;              /*   ER4        */
                    _UDWORD ER5:1;              /*   ER5        */
                    _UDWORD ER6:1;              /*   ER6        */
                    _UDWORD ER7:1;              /*   ER7        */
                    _UWORD :24;                 /*              */
                    } BIT;                      /*              */
             } DSTAT_ER;                        /*              */
       union {                                  /* DSTAT_END    */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD END0:1;             /*   END0       */
                    _UDWORD END1:1;             /*   END1       */
                    _UDWORD END2:1;             /*   END2       */
                    _UDWORD END3:1;             /*   END3       */
                    _UDWORD END4:1;             /*   END4       */
                    _UDWORD END5:1;             /*   END5       */
                    _UDWORD END6:1;             /*   END6       */
                    _UDWORD END7:1;             /*   END7       */
                    _UWORD :24;                 /*              */
                    } BIT;                      /*              */
             } DSTAT_END;                       /*              */
       union {                                  /* DSTAT_TC     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD TC0:1;              /*   TC0        */
                    _UDWORD TC1:1;              /*   TC1        */
                    _UDWORD TC2:1;              /*   TC2        */
                    _UDWORD TC3:1;              /*   TC3        */
                    _UDWORD TC4:1;              /*   TC4        */
                    _UDWORD TC5:1;              /*   TC5        */
                    _UDWORD TC6:1;              /*   TC6        */
                    _UDWORD TC7:1;              /*   TC7        */
                    _UWORD :24;                 /*              */
                    } BIT;                      /*              */
             } DSTAT_TC;                        /*              */
       union {                                  /* DSTAT_SUS    */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD SUS0:1;             /*   SUS0       */
                    _UDWORD SUS1:1;             /*   SUS1       */
                    _UDWORD SUS2:1;             /*   SUS2       */
                    _UDWORD SUS3:1;             /*   SUS3       */
                    _UDWORD SUS4:1;             /*   SUS4       */
                    _UDWORD SUS5:1;             /*   SUS5       */
                    _UDWORD SUS6:1;             /*   SUS6       */
                    _UDWORD SUS7:1;             /*   SUS7       */
                    _UWORD :24;                 /*              */
                    } BIT;                      /*              */
             } DSTAT_SUS;                       /*              */
};                                              /*              */

struct st_dmac_815 {                            /* struct DMAC  */
       union {                                  /* DCTRL        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD PR:1;               /*   PR         */
                    _UDWORD LVINT:1;            /*   LVINT      */
                    _UWORD :18;                 /*              */
                    _UDWORD LDCA:4;             /*   LDCA       */
                    _UWORD :4;                  /*              */
                    _UDWORD LWCA:4;             /*   LWCA       */
                    } BIT;                      /*              */
             } DCTRL;                           /*              */
       union {                                  /* DSTAT_EN     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD EN8:1;              /*   EN8        */
                    _UDWORD EN9:1;              /*   EN9        */
                    _UDWORD EN10:1;             /*   EN10       */
                    _UDWORD EN11:1;             /*   EN11       */
                    _UDWORD EN12:1;             /*   EN12       */
                    _UDWORD EN13:1;             /*   EN13       */
                    _UDWORD EN14:1;             /*   EN14       */
                    _UDWORD EN15:1;             /*   EN15       */
                    _UWORD :24;                 /*              */
                    } BIT;                      /*              */
             } DSTAT_EN;                        /*              */
       union {                                  /* DSTAT_ER     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD ER8:1;              /*   ER8        */
                    _UDWORD ER9:1;              /*   ER9        */
                    _UDWORD ER10:1;             /*   ER10       */
                    _UDWORD ER11:1;             /*   ER11       */
                    _UDWORD ER12:1;             /*   ER12       */
                    _UDWORD ER13:1;             /*   ER13       */
                    _UDWORD ER14:1;             /*   ER14       */
                    _UDWORD ER15:1;             /*   ER15       */
                    _UWORD :24;                 /*              */
                    } BIT;                      /*              */
             } DSTAT_ER;                        /*              */
       union {                                  /* DSTAT_END    */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD END8:1;             /*   END8       */
                    _UDWORD END9:1;             /*   END9       */
                    _UDWORD END10:1;            /*   END10      */
                    _UDWORD END11:1;            /*   END11      */
                    _UDWORD END12:1;            /*   END12      */
                    _UDWORD END13:1;            /*   END13      */
                    _UDWORD END14:1;            /*   END14      */
                    _UDWORD END15:1;            /*   END15      */
                    _UWORD :24;                 /*              */
                    } BIT;                      /*              */
             } DSTAT_END;                       /*              */
       union {                                  /* DSTAT_TC     */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD TC8:1;              /*   TC8        */
                    _UDWORD TC9:1;              /*   TC9        */
                    _UDWORD TC10:1;             /*   TC10       */
                    _UDWORD TC11:1;             /*   TC11       */
                    _UDWORD TC12:1;             /*   TC12       */
                    _UDWORD TC13:1;             /*   TC13       */
                    _UDWORD TC14:1;             /*   TC14       */
                    _UDWORD TC15:1;             /*   TC15       */
                    _UWORD :24;                 /*              */
                    } BIT;                      /*              */
             } DSTAT_TC;                        /*              */
       union {                                  /* DSTAT_SUS    */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD SUS8:1;             /*   SUS8       */
                    _UDWORD SUS9:1;             /*   SUS9       */
                    _UDWORD SUS10:1;            /*   SUS10      */
                    _UDWORD SUS11:1;            /*   SUS11      */
                    _UDWORD SUS12:1;            /*   SUS12      */
                    _UDWORD SUS13:1;            /*   SUS13      */
                    _UDWORD SUS14:1;            /*   SUS14      */
                    _UDWORD SUS15:1;            /*   SUS15      */
                    _UWORD :24;                 /*              */
                    } BIT;                      /*              */
             } DSTAT_SUS;                       /*              */
};                                              /*              */

struct st_dmac_01 {                             /* struct DMAC  */
       union {                                  /* DMARS        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD CH0_RID:2;          /*   CH0_RID    */
                    _UDWORD CH0_MID:7;          /*   CH0_MID    */
                    _UWORD :7;                  /*              */
                    _UDWORD CH1_RID:2;          /*   CH1_RID    */
                    _UDWORD CH1_MID:7;          /*   CH1_MID    */
                    _UWORD :7;                  /*              */
                    } BIT;                      /*              */
             } DMARS;                           /*              */
};                                              /*              */

struct st_dmac_23 {                             /* struct DMAC  */
       union {                                  /* DMARS        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD CH2_RID:2;          /*   CH2_RID    */
                    _UDWORD CH2_MID:7;          /*   CH2_MID    */
                    _UWORD :7;                  /*              */
                    _UDWORD CH3_RID:2;          /*   CH3_RID    */
                    _UDWORD CH3_MID:7;          /*   CH3_MID    */
                    _UWORD :7;                  /*              */
                    } BIT;                      /*              */
             } DMARS;                           /*              */
};                                              /*              */

struct st_dmac_45 {                             /* struct DMAC  */
       union {                                  /* DMARS        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD CH4_RID:2;          /*   CH4_RID    */
                    _UDWORD CH4_MID:7;          /*   CH4_MID    */
                    _UWORD :7;                  /*              */
                    _UDWORD CH5_RID:2;          /*   CH5_RID    */
                    _UDWORD CH5_MID:7;          /*   CH5_MID    */
                    _UWORD :7;                  /*              */
                    } BIT;                      /*              */
             } DMARS;                           /*              */
};                                              /*              */

struct st_dmac_67 {                             /* struct DMAC  */
       union {                                  /* DMARS        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD CH6_RID:2;          /*   CH6_RID    */
                    _UDWORD CH6_MID:7;          /*   CH6_MID    */
                    _UWORD :7;                  /*              */
                    _UDWORD CH7_RID:2;          /*   CH7_RID    */
                    _UDWORD CH7_MID:7;          /*   CH7_MID    */
                    _UWORD :7;                  /*              */
                    } BIT;                      /*              */
             } DMARS;                           /*              */
};                                              /*              */

struct st_dmac_89 {                             /* struct DMAC  */
       union {                                  /* DMARS        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD CH8_RID:2;          /*   CH8_RID    */
                    _UDWORD CH8_MID:7;          /*   CH8_MID    */
                    _UWORD :7;                  /*              */
                    _UDWORD CH9_RID:2;          /*   CH9_RID    */
                    _UDWORD CH9_MID:7;          /*   CH9_MID    */
                    _UWORD :7;                  /*              */
                    } BIT;                      /*              */
             } DMARS;                           /*              */
};                                              /*              */

struct st_dmac_1011 {                           /* struct DMAC  */
       union {                                  /* DMARS        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD CH10_RID:2;         /*   CH10_RID   */
                    _UDWORD CH10_MID:7;         /*   CH10_MID   */
                    _UWORD :7;                  /*              */
                    _UDWORD CH11_RID:2;         /*   CH11_RID   */
                    _UDWORD CH11_MID:7;         /*   CH11_MID   */
                    _UWORD :7;                  /*              */
                    } BIT;                      /*              */
             } DMARS;                           /*              */
};                                              /*              */

struct st_dmac_1213 {                           /* struct DMAC  */
       union {                                  /* DMARS        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD CH12_RID:2;         /*   CH12_RID   */
                    _UDWORD CH12_MID:7;         /*   CH12_MID   */
                    _UWORD :7;                  /*              */
                    _UDWORD CH13_RID:2;         /*   CH13_RID   */
                    _UDWORD CH13_MID:7;         /*   CH13_MID   */
                    _UWORD :7;                  /*              */
                    } BIT;                      /*              */
             } DMARS;                           /*              */
};                                              /*              */

struct st_dmac_1415 {                           /* struct DMAC  */
       union {                                  /* DMARS        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD CH14_RID:2;         /*   CH14_RID   */
                    _UDWORD CH14_MID:7;         /*   CH14_MID   */
                    _UWORD :7;                  /*              */
                    _UDWORD CH15_RID:2;         /*   CH15_RID   */
                    _UDWORD CH15_MID:7;         /*   CH15_MID   */
                    _UWORD :7;                  /*              */
                    } BIT;                      /*              */
             } DMARS;                           /*              */
};                                              /*              */

#define DMAC0  (*(volatile struct st_dmac_n *)0xE8200000)	/* DMAC0  Address */
#define DMAC1  (*(volatile struct st_dmac_n *)0xE8200040)	/* DMAC1  Address */
#define DMAC2  (*(volatile struct st_dmac_n *)0xE8200080)	/* DMAC2  Address */
#define DMAC3  (*(volatile struct st_dmac_n *)0xE82000C0)	/* DMAC3  Address */
#define DMAC4  (*(volatile struct st_dmac_n *)0xE8200100)	/* DMAC4  Address */
#define DMAC5  (*(volatile struct st_dmac_n *)0xE8200140)	/* DMAC5  Address */
#define DMAC6  (*(volatile struct st_dmac_n *)0xE8200180)	/* DMAC6  Address */
#define DMAC7  (*(volatile struct st_dmac_n *)0xE82001C0)	/* DMAC7  Address */
#define DMAC8  (*(volatile struct st_dmac_n *)0xE8200400)	/* DMAC8  Address */
#define DMAC9  (*(volatile struct st_dmac_n *)0xE8200440)	/* DMAC9  Address */
#define DMAC10 (*(volatile struct st_dmac_n *)0xE8200480)	/* DMAC10 Address */
#define DMAC11 (*(volatile struct st_dmac_n *)0xE82004C0)	/* DMAC11 Address */
#define DMAC12 (*(volatile struct st_dmac_n *)0xE8200500)	/* DMAC12 Address */
#define DMAC13 (*(volatile struct st_dmac_n *)0xE8200540)	/* DMAC13 Address */
#define DMAC14 (*(volatile struct st_dmac_n *)0xE8200580)	/* DMAC14 Address */
#define DMAC15 (*(volatile struct st_dmac_n *)0xE82005C0)	/* DMAC15 Address */

#define DMAC07   (*(volatile struct st_dmac_07   *)0xE8200300)	/* DMAC0-7  Address */
#define DMAC815  (*(volatile struct st_dmac_815  *)0xE8200700)	/* DMAC8-15 Address */

#define DMAC01   (*(volatile struct st_dmac_01   *)0xFCFE1000)	/* DMAC0-1   Address */
#define DMAC23   (*(volatile struct st_dmac_23   *)0xFCFE1004)	/* DMAC2-3   Address */
#define DMAC45   (*(volatile struct st_dmac_45   *)0xFCFE1008)	/* DMAC4-5   Address */
#define DMAC67   (*(volatile struct st_dmac_67   *)0xFCFE100C)	/* DMAC6-7   Address */
#define DMAC89   (*(volatile struct st_dmac_89   *)0xFCFE1010)	/* DMAC8-9   Address */
#define DMAC1011 (*(volatile struct st_dmac_1011 *)0xFCFE1014)	/* DMAC10-11 Address */
#define DMAC1213 (*(volatile struct st_dmac_1213 *)0xFCFE1018)	/* DMAC12-13 Address */
#define DMAC1415 (*(volatile struct st_dmac_1415 *)0xFCFE101C)	/* DMAC14-15 Address */

#endif /* __DMAC_IODEFINE_H__ */

/* End of File */
