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
* File Name     : bsc_iodefine.h
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
*         : 27.07.2012 0.01		参考資料：sec08_BSC_20120615.doc !!!TOSCORnに仕様書にないビット名あり!!!
*******************************************************************************/
#ifndef __BSC_IODEFINE_H__
#define __BSC_IODEFINE_H__

#include "typedefine.h"

typedef union {                                 /* CSnBCR       */
      _UDWORD LONG;                             /*  Long Access */
      struct {                                  /*  Bit Access  */
             _UDWORD :9;                        /*              */
             _UDWORD BSZ:2;                     /*   BSZ        */
             _UDWORD :1;                        /*              */
             _UDWORD TYPE:3;                    /*   TYPE       */
             _UDWORD :1;                        /*              */
             _UDWORD IWRRS:3;                   /*   IWRRS      */
             _UDWORD IWRRD:3;                   /*   IWRRD      */
             _UDWORD IWRWS:3;                   /*   IWRWS      */
             _UDWORD IWRWD:3;                   /*   IWRWD      */
             _UDWORD IWW:3;                     /*   IWW        */
             _UDWORD :1;                        /*              */
             } BIT;                             /*              */
} CSnBCR;                                       /*              */
typedef union {                                 /* TOSCORn      */
      _UDWORD LONG;                             /*  Long Access */
      struct {                                  /*  Bit Access  */
             _UDWORD xxx:16;                    /*   xxx        */	/* !!!ビット名決定次第、定義する!!! */
             _UDWORD :16;                       /*              */
              } BIT;                            /*              */
} TOSCORn;                                      /*              */

struct st_bsc {                                 /* struct BSC   */
       union {                                  /* CMNCR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD HIZCNT:1;           /*   HIZCNT     */
                    _UDWORD HIZMEM:1;           /*   HIZMEM     */
                    _UDWORD :7;                 /*              */
                    _UDWORD DPRTY:2;            /*   DPRTY      */
                    _UDWORD :13;                /*              */
                    _UDWORD AL0:1;              /*   AL0        */
                    _UDWORD :3;                 /*              */
                    _UDWORD TL0:1;              /*   TL0        */
                    _UDWORD :3;                 /*              */
                    } BIT;                      /*              */
             } CMNCR;                           /*              */
       CSnBCR CS0BCR;                           /* CS0BCR       */
       CSnBCR CS1BCR;                           /* CS1BCR       */
       CSnBCR CS2BCR;                           /* CS2BCR       */
       CSnBCR CS3BCR;                           /* CS3BCR       */
       CSnBCR CS4BCR;                           /* CS4BCR       */
       CSnBCR CS5BCR;                           /* CS5BCR       */
       _UBYTE wk0[12];                          /*              */
       union {                                  /* CS0WCR       */
             union {                            /* CS0WCR(NORMAL) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD HW:2;        /*   HW         */
                           _UDWORD :4;          /*              */
                           _UDWORD WM:1;        /*   WM         */
                           _UDWORD WR:4;        /*   WR         */
                           _UDWORD SW:2;        /*   SW         */
                           _UDWORD :7;          /*              */
                           _UDWORD BAS:1;       /*   BAS        */
                           _UDWORD :11;         /*              */
                           } BIT;               /*              */
                    } NORMAL;                   /*              */
             union {                            /* CS0WCR(BROM_ASY) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD :6;          /*              */
                           _UDWORD WM:1;        /*   WM         */
                           _UDWORD W:4;         /*   W          */
                           _UDWORD :5;          /*              */
                           _UDWORD BW:2;        /*   BW         */
                           _UDWORD :2;          /*              */
                           _UDWORD BST:2;       /*   BST        */
                           _UDWORD :10;         /*              */
                           } BIT;               /*              */
                    } BROM_ASY;                 /*              */
             union {                            /* CS0WCR(BROM_SY) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD :6;          /*              */
                           _UDWORD WM:1;        /*   WM         */
                           _UDWORD W:4;         /*   W          */
                           _UDWORD :5;          /*              */
                           _UDWORD BW:2;        /*   BW         */
                           _UDWORD :14;         /*              */
                           } BIT;               /*              */
                    } BROM_SY;                  /*              */
             } CS0WCR;                          /*              */
       union {                                  /* CS1WCR       */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD HW:2;        /*   HW         */
                           _UDWORD :4;          /*              */
                           _UDWORD WM:1;        /*   WM         */
                           _UDWORD WR:4;        /*   WR         */
                           _UDWORD SW:2;        /*   SW         */
                           _UDWORD :3;          /*              */
                           _UDWORD WW:3;        /*   WW         */
                           _UDWORD :1;          /*              */
                           _UDWORD BAS:1;       /*   BAS        */
                           _UDWORD :11;         /*              */
                           } BIT;               /*              */
             } CS1WCR;                          /*              */
       union {                                  /* CS2WCR       */
             union {                            /* CS2WCR(NORMAL) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD :6;          /*              */
                           _UDWORD WM:1;        /*   WM         */
                           _UDWORD WR:4;        /*   WR         */
                           _UDWORD :9;          /*              */
                           _UDWORD BAS:1;       /*   BAS        */
                           _UDWORD :11;         /*              */
                           } BIT;               /*              */
                    } NORMAL;                   /*              */
             union {                            /* CS2WCR(SDRAM) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD :7;          /*              */
                           _UDWORD A2CL:2;      /*   A2CL       */
                           _UDWORD :23;         /*              */
                           } BIT;               /*              */
                    } SDRAM;                    /*              */
             } CS2WCR;                          /*              */
       union {                                  /* CS3WCR       */
             union {                            /* CS3WCR(NORMAL) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD :6;          /*              */
                           _UDWORD WM:1;        /*   WM         */
                           _UDWORD WR:4;        /*   WR         */
                           _UDWORD :9;          /*              */
                           _UDWORD BAS:1;       /*   BAS        */
                           _UDWORD :11;         /*              */
                           } BIT;               /*              */
                    } NORMAL;                   /*              */
             union {                            /* CS3WCR(SDRAM) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD WTRC:2;      /*   WTRC       */
                           _UDWORD :1;          /*              */
                           _UDWORD TRWL:2;      /*   TRWL       */
                           _UDWORD :2;          /*              */
                           _UDWORD A3CL:2;      /*   A3CL       */
                           _UDWORD :1;          /*              */
                           _UDWORD WTRCD:2;     /*   WTRCD      */
                           _UDWORD :1;          /*              */
                           _UDWORD WTRP:2;      /*   WTRP       */
                           _UDWORD :17;         /*              */
                           } BIT;               /*              */
                    } SDRAM;                    /*              */
             } CS3WCR;                          /*              */
       union {                                  /* CS4WCR       */
             union {                            /* CS4WCR(NORMAL) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD HW:2;        /*   HW         */
                           _UDWORD :4;          /*              */
                           _UDWORD WM:1;        /*   WM         */
                           _UDWORD WR:4;        /*   WR         */
                           _UDWORD SW:2;        /*   SW         */
                           _UDWORD :3;          /*              */
                           _UDWORD WW:3;        /*   WW         */
                           _UDWORD :1;          /*              */
                           _UDWORD BAS:1;       /*   BAS        */
                           _UDWORD :11;         /*              */
                           } BIT;               /*              */
                    } NORMAL;                   /*              */
             union {                            /* CS4WCR(BROM_ASY) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD HW:2;        /*   HW         */
                           _UDWORD :4;          /*              */
                           _UDWORD WM:1;        /*   WM         */
                           _UDWORD W:4;         /*   W          */
                           _UDWORD SW:2;        /*   SW         */
                           _UDWORD :3;          /*              */
                           _UDWORD BW:2;        /*   BW         */
                           _UDWORD :2;          /*              */
                           _UDWORD BST:2;       /*   BST        */
                           _UDWORD :10;         /*              */
                           } BIT;               /*              */
                    } BROM_ASY;                 /*              */
             } CS4WCR;                          /*              */
       union {                                  /* CS5WCR       */
             union {                            /* CS5WCR(NORMAL) */
                    _UDWORD LONG;               /*  Long Access */
                    struct {                    /*  Bit Access  */
                           _UDWORD HW:2;        /*   HW         */
                           _UDWORD :4;          /*              */
                           _UDWORD WM:1;        /*   WM         */
                           _UDWORD WR:4;        /*   WR         */
                           _UDWORD SW:2;        /*   SW         */
                           _UDWORD :3;          /*              */
                           _UDWORD WW:3;        /*   WW         */
                           _UDWORD :1;          /*              */
                           _UDWORD MPXWBAS:1;   /*   MPXW/BAS   */
                           _UDWORD SZSEL:1;     /*   SZSEL      */
                           _UDWORD :10;         /*              */
                           } BIT;               /*              */
                    } NORMAL;                   /*              */
             } CS5WCR;                          /*              */
       _UBYTE wk1[12];                          /*              */
       union {                                  /* SDCR         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD A3COL:2;            /*   A3COL      */
                    _UDWORD :1;                 /*              */
                    _UDWORD A3ROW:2;            /*   A3ROW      */
                    _UDWORD :3;                 /*              */
                    _UDWORD BACTV:1;            /*   BACTV      */
                    _UDWORD PDOWN:1;            /*   PDOWN      */
                    _UDWORD RMODE:1;            /*   RMODE      */
                    _UDWORD RFSH:1;             /*   RFSH       */
                    _UDWORD :1;                 /*              */
                    _UDWORD DEEP:1;             /*   DEEP       */
                    _UDWORD :2;                 /*              */
                    _UDWORD A2COL:2;            /*   A2COL      */
                    _UDWORD :1;                 /*              */
                    _UDWORD A2ROW:2;            /*   A2ROW      */
                    _UDWORD :11;                /*              */
                    } BIT;                      /*              */
             } SDCR;                            /*              */
       union {                                  /* RTCSR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD RRC:3;              /*   RRC        */
                    _UDWORD CKS:3;              /*   CKS        */
                    _UDWORD CMIE:1;             /*   CMIE       */
                    _UDWORD CMF:1;              /*   CMF        */
                    _UDWORD :24;                /*              */
                    } BIT;                      /*              */
             } RTCSR;                           /*              */
       union {                                  /* RTCNT        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RTCNT;                           /*              */
       union {                                  /* RTCOR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD D:32;               /*   D          */
                    } BIT;                      /*              */
             } RTCOR;                           /*              */
       _UBYTE wk2[4];                           /*              */
       TOSCORn TOSCOR0;                         /* TOSCOR0      */
       TOSCORn TOSCOR1;                         /* TOSCOR1      */
       TOSCORn TOSCOR2;                         /* TOSCOR2      */
       TOSCORn TOSCOR3;                         /* TOSCOR3      */
       TOSCORn TOSCOR4;                         /* TOSCOR4      */
       TOSCORn TOSCOR5;                         /* TOSCOR5      */
       _UBYTE wk3[8];                           /*              */
       union {                                  /* TOSTR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD CS0TOSTF:1;         /*   CS0TOSTF   */
                    _UDWORD CS1TOSTF:1;         /*   CS1TOSTF   */
                    _UDWORD CS2TOSTF:1;         /*   CS2TOSTF   */
                    _UDWORD CS3TOSTF:1;         /*   CS3TOSTF   */
                    _UDWORD CS4TOSTF:1;         /*   CS4TOSTF   */
                    _UDWORD CS5TOSTF:1;         /*   CS5TOSTF   */
                    _UDWORD :26;                /*              */
                    } BIT;                      /*              */
             } TOSTR;                           /*              */
       union {                                  /* TOENR        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  Bit Access  */
                    _UDWORD CS0TOEN:1;          /*   CS0TOEN    */
                    _UDWORD CS1TOEN:1;          /*   CS1TOEN    */
                    _UDWORD CS2TOEN:1;          /*   CS2TOEN    */
                    _UDWORD CS3TOEN:1;          /*   CS3TOEN    */
                    _UDWORD CS4TOEN:1;          /*   CS4TOEN    */
                    _UDWORD CS5TOEN:1;          /*   CS5TOEN    */
                    _UDWORD :26;                /*              */
                    } BIT;                      /*              */
             } TOENR;                           /*              */
};                                              /*              */

#define	BSC		(*(volatile struct st_bsc *)0x3FFFC000)   /* BSC Address */


#endif /* __BSC_IODEFINE_H__ */

/* End of File */
