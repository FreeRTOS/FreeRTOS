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
*   File Name   : pfc_iodefine.h
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
#ifndef __PFC_IODEFINE_H__
#define __PFC_IODEFINE_H__

#include "typedefine.h"

struct st_pfc_n {                              /* struct PFC    */
       union {                                  /* Pn           */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD Pn0:1;               /*              */
                    _UWORD Pn1:1;               /*              */
                    _UWORD Pn2:1;               /*              */
                    _UWORD Pn3:1;               /*              */
                    _UWORD Pn4:1;               /*              */
                    _UWORD Pn5:1;               /*              */
                    _UWORD Pn6:1;               /*              */
                    _UWORD Pn7:1;               /*              */
                    _UWORD Pn8:1;               /*              */
                    _UWORD Pn9:1;               /*              */
                    _UWORD Pn10:1;              /*              */
                    _UWORD Pn11:1;              /*              */
                    _UWORD Pn12:1;              /*              */
                    _UWORD Pn13:1;              /*              */
                    _UWORD Pn14:1;              /*              */
                    _UWORD Pn15:1;              /*              */
                    } BIT;                      /*              */
             } Pn;                              /*              */
       _UBYTE wk0[0x100-2];                     /*              */
       union {                                  /* PSRn         */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  WORD Access */
                    _UDWORD ENABLE:16;          /*              */
                    _UDWORD SET:16;             /*              */
                    } SET;
             struct {                           /*  Bit Access  */
                    _UDWORD PSRn0:1;            /*              */
                    _UDWORD PSRn1:1;            /*              */
                    _UDWORD PSRn2:1;            /*              */
                    _UDWORD PSRn3:1;            /*              */
                    _UDWORD PSRn4:1;            /*              */
                    _UDWORD PSRn5:1;            /*              */
                    _UDWORD PSRn6:1;            /*              */
                    _UDWORD PSRn7:1;            /*              */
                    _UDWORD PSRn8:1;            /*              */
                    _UDWORD PSRn9:1;            /*              */
                    _UDWORD PSRn10:1;           /*              */
                    _UDWORD PSRn11:1;           /*              */
                    _UDWORD PSRn12:1;           /*              */
                    _UDWORD PSRn13:1;           /*              */
                    _UDWORD PSRn14:1;           /*              */
                    _UDWORD PSRn15:1;           /*              */
                    _UDWORD PSRn16:1;           /*              */
                    _UDWORD PSRn17:1;           /*              */
                    _UDWORD PSRn18:1;           /*              */
                    _UDWORD PSRn19:1;           /*              */
                    _UDWORD PSRn20:1;           /*              */
                    _UDWORD PSRn21:1;           /*              */
                    _UDWORD PSRn22:1;           /*              */
                    _UDWORD PSRn23:1;           /*              */
                    _UDWORD PSRn24:1;           /*              */
                    _UDWORD PSRn25:1;           /*              */
                    _UDWORD PSRn26:1;           /*              */
                    _UDWORD PSRn27:1;           /*              */
                    _UDWORD PSRn28:1;           /*              */
                    _UDWORD PSRn29:1;           /*              */
                    _UDWORD PSRn30:1;           /*              */
                    _UDWORD PSRn31:1;           /*              */
                    } BIT;                      /*              */
             } PSRn;                            /*              */
       _UBYTE wk1[0x100-4];                     /*              */
       union {                                  /* PPRn         */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PPRn0:1;             /*              */
                    _UWORD PPRn1:1;             /*              */
                    _UWORD PPRn2:1;             /*              */
                    _UWORD PPRn3:1;             /*              */
                    _UWORD PPRn4:1;             /*              */
                    _UWORD PPRn5:1;             /*              */
                    _UWORD PPRn6:1;             /*              */
                    _UWORD PPRn7:1;             /*              */
                    _UWORD PPRn8:1;             /*              */
                    _UWORD PPRn9:1;             /*              */
                    _UWORD PPRn10:1;            /*              */
                    _UWORD PPRn11:1;            /*              */
                    _UWORD PPRn12:1;            /*              */
                    _UWORD PPRn13:1;            /*              */
                    _UWORD PPRn14:1;            /*              */
                    _UWORD PPRn15:1;            /*              */
                    } BIT;                      /*              */
             } PPRn;                            /*              */
       _UBYTE wk2[0x100-2];                     /*              */
       union {                                  /* PMn          */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PMn0:1;              /*              */
                    _UWORD PMn1:1;              /*              */
                    _UWORD PMn2:1;              /*              */
                    _UWORD PMn3:1;              /*              */
                    _UWORD PMn4:1;              /*              */
                    _UWORD PMn5:1;              /*              */
                    _UWORD PMn6:1;              /*              */
                    _UWORD PMn7:1;              /*              */
                    _UWORD PMn8:1;              /*              */
                    _UWORD PMn9:1;              /*              */
                    _UWORD PMn10:1;             /*              */
                    _UWORD PMn11:1;             /*              */
                    _UWORD PMn12:1;             /*              */
                    _UWORD PMn13:1;             /*              */
                    _UWORD PMn14:1;             /*              */
                    _UWORD PMn15:1;             /*              */
                    } BIT;                      /*              */
             } PMn;                             /*              */
       _UBYTE wk3[0x100-2];                     /*              */
       union {                                  /* PMCn         */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PMCn0:1;             /*              */
                    _UWORD PMCn1:1;             /*              */
                    _UWORD PMCn2:1;             /*              */
                    _UWORD PMCn3:1;             /*              */
                    _UWORD PMCn4:1;             /*              */
                    _UWORD PMCn5:1;             /*              */
                    _UWORD PMCn6:1;             /*              */
                    _UWORD PMCn7:1;             /*              */
                    _UWORD PMCn8:1;             /*              */
                    _UWORD PMCn9:1;             /*              */
                    _UWORD PMCn10:1;            /*              */
                    _UWORD PMCn11:1;            /*              */
                    _UWORD PMCn12:1;            /*              */
                    _UWORD PMCn13:1;            /*              */
                    _UWORD PMCn14:1;            /*              */
                    _UWORD PMCn15:1;            /*              */
                     } BIT;                      /*              */
             } PMCn;                            /*              */
       _UBYTE wk4[0x100-2];                     /*              */
       union {                                  /* PFCn         */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PFCn0:1;             /*              */
                    _UWORD PFCn1:1;             /*              */
                    _UWORD PFCn2:1;             /*              */
                    _UWORD PFCn3:1;             /*              */
                    _UWORD PFCn4:1;             /*              */
                    _UWORD PFCn5:1;             /*              */
                    _UWORD PFCn6:1;             /*              */
                    _UWORD PFCn7:1;             /*              */
                    _UWORD PFCn8:1;             /*              */
                    _UWORD PFCn9:1;             /*              */
                    _UWORD PFCn10:1;            /*              */
                    _UWORD PFCn11:1;            /*              */
                    _UWORD PFCn12:1;            /*              */
                    _UWORD PFCn13:1;            /*              */
                    _UWORD PFCn14:1;            /*              */
                    _UWORD PFCn15:1;            /*              */
                    } BIT;                      /*              */
             } PFCn;                            /*              */
       _UBYTE wk5[0x100-2];                     /*              */
       union {                                  /* PFCEn        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PFCEn0:1;            /*              */
                    _UWORD PFCEn1:1;            /*              */
                    _UWORD PFCEn2:1;            /*              */
                    _UWORD PFCEn3:1;            /*              */
                    _UWORD PFCEn4:1;            /*              */
                    _UWORD PFCEn5:1;            /*              */
                    _UWORD PFCEn6:1;            /*              */
                    _UWORD PFCEn7:1;            /*              */
                    _UWORD PFCEn8:1;            /*              */
                    _UWORD PFCEn9:1;            /*              */
                    _UWORD PFCEn10:1;           /*              */
                    _UWORD PFCEn11:1;           /*              */
                    _UWORD PFCEn12:1;           /*              */
                    _UWORD PFCEn13:1;           /*              */
                    _UWORD PFCEn14:1;           /*              */
                    _UWORD PFCEn15:1;           /*              */
                    } BIT;                      /*              */
             } PFCEn;                           /*              */
       _UBYTE wk6[0x100-2];                     /*              */
       union {                                  /* PNOTn        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PNOTn0:1;            /*              */
                    _UWORD PNOTn1:1;            /*              */
                    _UWORD PNOTn2:1;            /*              */
                    _UWORD PNOTn3:1;            /*              */
                    _UWORD PNOTn4:1;            /*              */
                    _UWORD PNOTn5:1;            /*              */
                    _UWORD PNOTn6:1;            /*              */
                    _UWORD PNOTn7:1;            /*              */
                    _UWORD PNOTn8:1;            /*              */
                    _UWORD PNOTn9:1;            /*              */
                    _UWORD PNOTn10:1;           /*              */
                    _UWORD PNOTn11:1;           /*              */
                    _UWORD PNOTn12:1;           /*              */
                    _UWORD PNOTn13:1;           /*              */
                    _UWORD PNOTn14:1;           /*              */
                    _UWORD PNOTn15:1;           /*              */
                    } BIT;                      /*              */
             } PNOTn;                           /*              */
       _UBYTE wk7[0x100-2];                     /*              */
       union {                                  /* PMSRn        */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  WORD Access */
                    _UDWORD ENABLE:16;          /*              */
                    _UDWORD SET:16;             /*              */
                    } SET;
             struct {                           /*  Bit Access  */
                    _UDWORD PMSRn0:1;           /*              */
                    _UDWORD PMSRn1:1;           /*              */
                    _UDWORD PMSRn2:1;           /*              */
                    _UDWORD PMSRn3:1;           /*              */
                    _UDWORD PMSRn4:1;           /*              */
                    _UDWORD PMSRn5:1;           /*              */
                    _UDWORD PMSRn6:1;           /*              */
                    _UDWORD PMSRn7:1;           /*              */
                    _UDWORD PMSRn8:1;           /*              */
                    _UDWORD PMSRn9:1;           /*              */
                    _UDWORD PMSRn10:1;          /*              */
                    _UDWORD PMSRn11:1;          /*              */
                    _UDWORD PMSRn12:1;          /*              */
                    _UDWORD PMSRn13:1;          /*              */
                    _UDWORD PMSRn14:1;          /*              */
                    _UDWORD PMSRn15:1;          /*              */
                    _UDWORD PMSRn16:1;          /*              */
                    _UDWORD PMSRn17:1;          /*              */
                    _UDWORD PMSRn18:1;          /*              */
                    _UDWORD PMSRn19:1;          /*              */
                    _UDWORD PMSRn20:1;          /*              */
                    _UDWORD PMSRn21:1;          /*              */
                    _UDWORD PMSRn22:1;          /*              */
                    _UDWORD PMSRn23:1;          /*              */
                    _UDWORD PMSRn24:1;          /*              */
                    _UDWORD PMSRn25:1;          /*              */
                    _UDWORD PMSRn26:1;          /*              */
                    _UDWORD PMSRn27:1;          /*              */
                    _UDWORD PMSRn28:1;          /*              */
                    _UDWORD PMSRn29:1;          /*              */
                    _UDWORD PMSRn30:1;          /*              */
                    _UDWORD PMSRn31:1;          /*              */
                    } BIT;                      /*              */
             } PMSRn;                           /*              */
       _UBYTE wk8[0x100-4];                     /*              */
       union {                                  /* PMCSRn       */
             _UDWORD LONG;                      /*  Long Access */
             struct {                           /*  WORD Access */
                    _UDWORD ENABLE:16;          /*              */
                    _UDWORD SET:16;             /*              */
                    } SET;
             struct {                           /*  Bit Access  */
                    _UDWORD PMCSRn0:1;          /*              */
                    _UDWORD PMCSRn1:1;          /*              */
                    _UDWORD PMCSRn2:1;          /*              */
                    _UDWORD PMCSRn3:1;          /*              */
                    _UDWORD PMCSRn4:1;          /*              */
                    _UDWORD PMCSRn5:1;          /*              */
                    _UDWORD PMCSRn6:1;          /*              */
                    _UDWORD PMCSRn7:1;          /*              */
                    _UDWORD PMCSRn8:1;          /*              */
                    _UDWORD PMCSRn9:1;          /*              */
                    _UDWORD PMCSRn10:1;         /*              */
                    _UDWORD PMCSRn11:1;         /*              */
                    _UDWORD PMCSRn12:1;         /*              */
                    _UDWORD PMCSRn13:1;         /*              */
                    _UDWORD PMCSRn14:1;         /*              */
                    _UDWORD PMCSRn15:1;         /*              */
                    _UDWORD PMCSRn16:1;         /*              */
                    _UDWORD PMCSRn17:1;         /*              */
                    _UDWORD PMCSRn18:1;         /*              */
                    _UDWORD PMCSRn19:1;         /*              */
                    _UDWORD PMCSRn20:1;         /*              */
                    _UDWORD PMCSRn21:1;         /*              */
                    _UDWORD PMCSRn22:1;         /*              */
                    _UDWORD PMCSRn23:1;         /*              */
                    _UDWORD PMCSRn24:1;         /*              */
                    _UDWORD PMCSRn25:1;         /*              */
                    _UDWORD PMCSRn26:1;         /*              */
                    _UDWORD PMCSRn27:1;         /*              */
                    _UDWORD PMCSRn28:1;         /*              */
                    _UDWORD PMCSRn29:1;         /*              */
                    _UDWORD PMCSRn30:1;         /*              */
                    _UDWORD PMCSRn31:1;         /*              */
                    } BIT;                      /*              */
             } PMCSRn;                          /*              */
       _UBYTE wk9[0x100-4];                     /*              */
       union {                                  /* PFACEn       */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PFCAEn0:1;           /*              */
                    _UWORD PFCAEn1:1;           /*              */
                    _UWORD PFCAEn2:1;           /*              */
                    _UWORD PFCAEn3:1;           /*              */
                    _UWORD PFCAEn4:1;           /*              */
                    _UWORD PFCAEn5:1;           /*              */
                    _UWORD PFCAEn6:1;           /*              */
                    _UWORD PFCAEn7:1;           /*              */
                    _UWORD PFCAEn8:1;           /*              */
                    _UWORD PFCAEn9:1;           /*              */
                    _UWORD PFCAEn10:1;          /*              */
                    _UWORD PFCAEn11:1;          /*              */
                    _UWORD PFCAEn12:1;          /*              */
                    _UWORD PFCAEn13:1;          /*              */
                    _UWORD PFCAEn14:1;          /*              */
                    _UWORD PFCAEn15:1;          /*              */
                    } BIT;                      /*              */
             } PFCAEn;                          /*              */
       _UBYTE wk10[0x4000-0xa00-2];             /*              */
       union {                                  /* PIBCn        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PIBCn0:1;            /*              */
                    _UWORD PIBCn1:1;            /*              */
                    _UWORD PIBCn2:1;            /*              */
                    _UWORD PIBCn3:1;            /*              */
                    _UWORD PIBCn4:1;            /*              */
                    _UWORD PIBCn5:1;            /*              */
                    _UWORD PIBCn6:1;            /*              */
                    _UWORD PIBCn7:1;            /*              */
                    _UWORD PIBCn8:1;            /*              */
                    _UWORD PIBCn9:1;            /*              */
                    _UWORD PIBCn10:1;           /*              */
                    _UWORD PIBCn11:1;           /*              */
                    _UWORD PIBCn12:1;           /*              */
                    _UWORD PIBCn13:1;           /*              */
                    _UWORD PIBCn14:1;           /*              */
                    _UWORD PIBCn15:1;           /*              */
                    } BIT;                      /*              */
             } PIBCn;                           /*              */
       _UBYTE wk11[0x100-2];                    /*              */
       union {                                  /* PBDCn        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PBDCn0:1;            /*              */
                    _UWORD PBDCn1:1;            /*              */
                    _UWORD PBDCn2:1;            /*              */
                    _UWORD PBDCn3:1;            /*              */
                    _UWORD PBDCn4:1;            /*              */
                    _UWORD PBDCn5:1;            /*              */
                    _UWORD PBDCn6:1;            /*              */
                    _UWORD PBDCn7:1;            /*              */
                    _UWORD PBDCn8:1;            /*              */
                    _UWORD PBDCn9:1;            /*              */
                    _UWORD PBDCn10:1;           /*              */
                    _UWORD PBDCn11:1;           /*              */
                    _UWORD PBDCn12:1;           /*              */
                    _UWORD PBDCn13:1;           /*              */
                    _UWORD PBDCn14:1;           /*              */
                    _UWORD PBDCn15:1;           /*              */
                    } BIT;                      /*              */
             } PBDCn;                           /*              */
       _UBYTE wk12[0x100-2];                    /*              */
       union {                                  /* PIPCn        */
             _UWORD WORD;                       /*  Word Access */
             struct {                           /*  Bit Access  */
                    _UWORD PIPCn0:1;            /*              */
                    _UWORD PIPCn1:1;            /*              */
                    _UWORD PIPCn2:1;            /*              */
                    _UWORD PIPCn3:1;            /*              */
                    _UWORD PIPCn4:1;            /*              */
                    _UWORD PIPCn5:1;            /*              */
                    _UWORD PIPCn6:1;            /*              */
                    _UWORD PIPCn7:1;            /*              */
                    _UWORD PIPCn8:1;            /*              */
                    _UWORD PIPCn9:1;            /*              */
                    _UWORD PIPCn10:1;           /*              */
                    _UWORD PIPCn11:1;           /*              */
                    _UWORD PIPCn12:1;           /*              */
                    _UWORD PIPCn13:1;           /*              */
                    _UWORD PIPCn14:1;           /*              */
                    _UWORD PIPCn15:1;           /*              */
                    } BIT;                      /*              */
             } PIPCn;                           /*              */
       _UBYTE wk13[0x100-2];                    /*              */
};                                              /*              */

#define PORTn_BASE	0xFCFE3000

#define	PORT0		(*(volatile struct st_pfc_n *)(PORTn_BASE + (4 *  0)))   /* PORT  0 Address */
#define	PORT1		(*(volatile struct st_pfc_n *)(PORTn_BASE + (4 *  1)))   /* PORT  1 Address */
#define	PORT2		(*(volatile struct st_pfc_n *)(PORTn_BASE + (4 *  2)))   /* PORT  2 Address */
#define	PORT3		(*(volatile struct st_pfc_n *)(PORTn_BASE + (4 *  3)))   /* PORT  3 Address */
#define	PORT4		(*(volatile struct st_pfc_n *)(PORTn_BASE + (4 *  4)))   /* PORT  4 Address */
#define	PORT5		(*(volatile struct st_pfc_n *)(PORTn_BASE + (4 *  5)))   /* PORT  5 Address */
#define	PORT6		(*(volatile struct st_pfc_n *)(PORTn_BASE + (4 *  6)))   /* PORT  6 Address */
#define	PORT7		(*(volatile struct st_pfc_n *)(PORTn_BASE + (4 *  7)))   /* PORT  7 Address */
#define	PORT8		(*(volatile struct st_pfc_n *)(PORTn_BASE + (4 *  8)))   /* PORT  8 Address */
#define	PORT9		(*(volatile struct st_pfc_n *)(PORTn_BASE + (4 *  9)))   /* PORT  9 Address */
#define	PORT10		(*(volatile struct st_pfc_n *)(PORTn_BASE + (4 * 10)))   /* PORT 10 Address */
#define	PORT11		(*(volatile struct st_pfc_n *)(PORTn_BASE + (4 * 11)))   /* PORT 11 Address */


#endif /* __PFC_IODEFINE_H__ */

/* End of File */
