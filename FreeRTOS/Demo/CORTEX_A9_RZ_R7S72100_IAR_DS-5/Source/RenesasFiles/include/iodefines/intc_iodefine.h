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
* File Name     : intc_iodefine.h
* Version       : 0.01
* Device(s)     : Aragon
* Tool-Chain    : DS-5 Ver 5.13
*                 ARM Complier 
*               : 
* H/W Platform  : Aragon CPU Board
* Description   : Aragon Sample Program vecotr.s
*******************************************************************************/
/*******************************************************************************
* History : DD.MM.YYYY Version Description
*******************************************************************************/
#ifndef __INTC_IODEFINE_H__
#define __INTC_IODEFINE_H__

#include "typedefine.h"

typedef union {                                        /* ICDxxx0      */
       _UDWORD LONG;                                   /*  Long Access */
       struct {                                        /*  Bit Access  */
             _UDWORD SW0:1;                            /*   SW0        */
             _UDWORD SW1:1;                            /*   SW1        */
             _UDWORD SW2:1;                            /*   SW2        */
             _UDWORD SW3:1;                            /*   SW3        */
             _UDWORD SW4:1;                            /*   SW4        */
             _UDWORD SW5:1;                            /*   SW5        */
             _UDWORD SW6:1;                            /*   SW6        */
             _UDWORD SW7:1;                            /*   SW7        */
             _UDWORD SW8:1;                            /*   SW8        */
             _UDWORD SW9:1;                            /*   SW9        */
             _UDWORD SW10:1;                           /*   SW10       */
             _UDWORD SW11:1;                           /*   SW11       */
             _UDWORD SW12:1;                           /*   SW12       */
             _UDWORD SW13:1;                           /*   SW13       */
             _UDWORD SW14:1;                           /*   SW14       */
             _UDWORD SW15:1;                           /*   SW15       */
             _UDWORD PMUIRQ0:1;                        /*   PMUIRQ0    */
             _UDWORD COMMRX0:1;                        /*   COMMRX0    */
             _UDWORD COMMTX0:1;                        /*   COMMTX0    */
             _UDWORD CTIIRQ0:1;                        /*   CTIIRQ0    */
             _UDWORD :12;                              /*              */
             } BIT;                                    /*              */
} ICDxxx0;                                             /*              */
typedef union {                                        /* ICDxxx1      */
       _UDWORD LONG;                                   /*  Long Access */
       struct {                                        /*  Bit Access  */
             _UDWORD IRQ0:1;                           /*   IRQ0       */
             _UDWORD IRQ1:1;                           /*   IRQ1       */
             _UDWORD IRQ2:1;                           /*   IRQ2       */
             _UDWORD IRQ3:1;                           /*   IRQ3       */
             _UDWORD IRQ4:1;                           /*   IRQ4       */
             _UDWORD IRQ5:1;                           /*   IRQ5       */
             _UDWORD IRQ6:1;                           /*   IRQ6       */
             _UDWORD IRQ7:1;                           /*   IRQ7       */
             _UDWORD PL310ERR:1;                       /*   PL310ERR   */
             _UDWORD DMAINT0:1;                        /*   DMAINT0    */
             _UDWORD DMAINT1:1;                        /*   DMAINT1    */
             _UDWORD DMAINT2:1;                        /*   DMAINT2    */
             _UDWORD DMAINT3:1;                        /*   DMAINT3    */
             _UDWORD DMAINT4:1;                        /*   DMAINT4    */
             _UDWORD DMAINT5:1;                        /*   DMAINT5    */
             _UDWORD DMAINT6:1;                        /*   DMAINT6    */
             _UDWORD DMAINT7:1;                        /*   DMAINT7    */
             _UDWORD DMAINT8:1;                        /*   DMAINT8    */
             _UDWORD DMAINT9:1;                        /*   DMAINT9    */
             _UDWORD DMAINT10:1;                       /*   DMAINT10   */
             _UDWORD DMAINT11:1;                       /*   DMAINT11   */
             _UDWORD DMAINT12:1;                       /*   DMAINT12   */
             _UDWORD DMAINT13:1;                       /*   DMAINT13   */
             _UDWORD DMAINT14:1;                       /*   DMAINT14   */
             _UDWORD DMAINT15:1;                       /*   DMAINT15   */
             _UDWORD DMAERR:1;                         /*   DMAERR     */
             _UDWORD :6;                               /*              */
             } BIT;                                    /*              */
} ICDxxx1;                                             /*              */
typedef union {                                        /* ICDxxx2      */
       _UDWORD LONG;                                   /*  Long Access */
       struct {                                        /*  Bit Access  */
             _UDWORD :9;                               /*              */
             _UDWORD USBI0:1;                          /*   USBI0      */
             _UDWORD USBI1:1;                          /*   USBI1      */
             _UDWORD S0_VI_VSYNC0:1;                   /*   S0_VI_VSYNC0 */
             _UDWORD S0_LO_VSYNC0:1;                   /*   S0_LO_VSYNC0 */
             _UDWORD S0_VSYNCERR0:1;                   /*   S0_VSYNCERR0 */
             _UDWORD GR3_VLINE0:1;                     /*   GR3_VLINE0 */
             _UDWORD S0_VFIELD0:1;                     /*   S0_VFIELD0 */
             _UDWORD IV1_VBUFERR0:1;                   /*   IV1_VBUFERR0 */
             _UDWORD IV3_VBUFERR0:1;                   /*   IV3_VBUFERR0 */
             _UDWORD IV5_VBUFERR0:1;                   /*   IV5_VBUFERR0 */
             _UDWORD IV6_VBUFERR0:1;                   /*   IV6_VBUFERR0 */
             _UDWORD S0_WLINE0:1;                      /*   S0_WLINE0  */
             _UDWORD S1_VI_VSYNC0:1;                   /*   S1_VI_VSYNC0 */
             _UDWORD S1_LO_VSYNC0:1;                   /*   S1_LO_VSYNC0 */
             _UDWORD S1_VSYNCERR0:1;                   /*   S1_VSYNCERR0 */
             _UDWORD S1_VFIELD0:1;                     /*   S1_VFIELD0 */
             _UDWORD IV2_VBUFERR0:1;                   /*   IV2_VBUFERR0 */
             _UDWORD IV4_VBUFERR0:1;                   /*   IV4_VBUFERR0 */
             _UDWORD S1_WLINE0:1;                      /*   S1_WLINE0  */
             _UDWORD OIR_VI_VSYNC0:1;                  /*   OIR_VI_VSYNC0 */
             _UDWORD OIR_LO_VSYNC0:1;                  /*   OIR_LO_VSYNC0 */
             _UDWORD OIR_VSYNCERR0:1;                  /*   OIR_VSYNCERR0 */
             _UDWORD OIR_VFIELD0:1;                    /*   OIR_VFIELD0 */
             } BIT;                                    /*              */
} ICDxxx2;                                             /*              */
typedef union {                                        /* ICDxxx3      */
       _UDWORD LONG;                                   /*  Long Access */
       struct {                                        /*  Bit Access  */
             _UDWORD IV7_VBUFERR0:1;                   /*   IV7_VBUFERR0 */
             _UDWORD IV8_VBUFERR0:1;                   /*   IV8_VBUFERR0 */
             _UDWORD OIR_WLINE0:1;                     /*   OIR_WLINE0 */
             _UDWORD S0_VI_VSYNC1:1;                   /*   S0_VI_VSYNC1 */
             _UDWORD S0_LO_VSYNC1:1;                   /*   S0_LO_VSYNC1 */
             _UDWORD S0_VSYNCERR1:1;                   /*   S0_VSYNCERR1 */
             _UDWORD GR3_VLINE1:1;                     /*   GR3_VLINE1 */
             _UDWORD S0_VFIELD1:1;                     /*   S0_VFIELD1 */
             _UDWORD IV1_VBUFERR1:1;                   /*   IV1_VBUFERR1 */
             _UDWORD IV3_VBUFERR1:1;                   /*   IV3_VBUFERR1 */
             _UDWORD IV5_VBUFERR1:1;                   /*   IV5_VBUFERR1 */
             _UDWORD IV6_VBUFERR1:1;                   /*   IV6_VBUFERR1 */
             _UDWORD S0_WLINE1:1;                      /*   S0_WLINE1  */
             _UDWORD S1_VI_VSYNC1:1;                   /*   S1_VI_VSYNC1 */
             _UDWORD S1_LO_VSYNC1:1;                   /*   S1_LO_VSYNC1 */
             _UDWORD S1_VSYNCERR1:1;                   /*   S1_VSYNCERR1 */
             _UDWORD S1_VFIELD1:1;                     /*   S1_VFIELD1 */
             _UDWORD IV2_VBUFERR1:1;                   /*   IV2_VBUFERR1 */
             _UDWORD IV4_VBUFERR1:1;                   /*   IV4_VBUFERR1 */
             _UDWORD S1_WLINE1:1;                      /*   S1_WLINE1  */
             _UDWORD OIR_VI_VSYNC1:1;                  /*   OIR_VI_VSYNC1 */
             _UDWORD OIR_LO_VSYNC1:1;                  /*   OIR_LO_VSYNC1 */
             _UDWORD OIR_VLINE1:1;                     /*   OIR_VLINE1 */
             _UDWORD OIR_VFIELD1:1;                    /*   OIR_VFIELD1 */
             _UDWORD IV7_VBUFERR1:1;                   /*   IV7_VBUFERR1 */
             _UDWORD IV8_VBUFERR1:1;                   /*   IV8_VBUFERR1 */
             _UDWORD OIR_WLINE1:1;                     /*   OIR_WLINE1 */
             _UDWORD IMRDI:1;                          /*   IMRDI      */
             _UDWORD IMR2I0:1;                         /*   IMR2I0     */
             _UDWORD IMR2I1:1;                         /*   IMR2I1     */
             _UDWORD JEDI:1;                           /*   JEDI       */
             _UDWORD JDTI:1;                           /*   JDTI       */
             } BIT;                                    /*              */
} ICDxxx3;                                             /*              */
typedef union {                                        /* ICDxxx4      */
       _UDWORD LONG;                                   /*  Long Access */
       struct {                                        /*  Bit Access  */
             _UDWORD CMP0:1;                           /*   CMP0       */
             _UDWORD CMP1:1;                           /*   CMP1       */
             _UDWORD INT0:1;                           /*   INT0       */
             _UDWORD INT1:1;                           /*   INT1       */
             _UDWORD INT2:1;                           /*   INT2       */
             _UDWORD INT3:1;                           /*   INT3       */
             _UDWORD OSTMI0:1;                         /*   OSTMI0     */
             _UDWORD OSTMI1:1;                         /*   OSTMI1     */
             _UDWORD CMI:1;                            /*   CMI        */
             _UDWORD WTOUT:1;                          /*   WTOUT      */
             _UDWORD ITI:1;                            /*   ITI        */
             _UDWORD TGI0A:1;                          /*   TGI0A      */
             _UDWORD TGI0B:1;                          /*   TGI0B      */
             _UDWORD TGI0C:1;                          /*   TGI0C      */
             _UDWORD TGI0D:1;                          /*   TGI0D      */
             _UDWORD TGI0V:1;                          /*   TGI0V      */
             _UDWORD TGI0E:1;                          /*   TGI0E      */
             _UDWORD TGI0F:1;                          /*   TGI0F      */
             _UDWORD TGI1A:1;                          /*   TGI1A      */
             _UDWORD TGI1B:1;                          /*   TGI1B      */
             _UDWORD TGI1V:1;                          /*   TGI1V      */
             _UDWORD TGI1U:1;                          /*   TGI1U      */
             _UDWORD TGI2A:1;                          /*   TGI2A      */
             _UDWORD TGI2B:1;                          /*   TGI2B      */
             _UDWORD TGI2V:1;                          /*   TGI2V      */
             _UDWORD TGI2U:1;                          /*   TGI2U      */
             _UDWORD TGI3A:1;                          /*   TGI3A      */
             _UDWORD TGI3B:1;                          /*   TGI3B      */
             _UDWORD TGI3C:1;                          /*   TGI3C      */
             _UDWORD TGI3D:1;                          /*   TGI3D      */
             _UDWORD TGI3V:1;                          /*   TGI3V      */
             _UDWORD TGI4A:1;                          /*   TGI4A      */
             } BIT;                                    /*              */
} ICDxxx4;                                             /*              */
typedef union {                                        /* ICDxxx5      */
       _UDWORD LONG;                                   /*  Long Access */
       struct {                                        /*  Bit Access  */
             _UDWORD TGI4B:1;                          /*   TGI4B      */
             _UDWORD TGI4C:1;                          /*   TGI4C      */
             _UDWORD TGI4D:1;                          /*   TGI4D      */
             _UDWORD TGI4V:1;                          /*   TGI4V      */
             _UDWORD CMI1:1;                           /*   CMI1       */
             _UDWORD CMI2:1;                           /*   CMI2       */
             _UDWORD SGDEI0:1;                         /*   SGDEI0     */
             _UDWORD SGDEI1:1;                         /*   SGDEI1     */
             _UDWORD SGDEI2:1;                         /*   SGDEI2     */
             _UDWORD SGDEI3:1;                         /*   SGDEI3     */
             _UDWORD ADI:1;                            /*   ADI        */
             _UDWORD ADWAR:1;                          /*   ADWAR      */
             _UDWORD SSII0:1;                          /*   SSII0      */
             _UDWORD SSIRXI0:1;                        /*   SSIRXI0    */
             _UDWORD SSITXI0:1;                        /*   SSITXI0    */
             _UDWORD SSII1:1;                          /*   SSII1      */
             _UDWORD SSIRXI1:1;                        /*   SSIRXI1    */
             _UDWORD SSITXI1:1;                        /*   SSITXI1    */
             _UDWORD SSII2:1;                          /*   SSII2      */
             _UDWORD SSIRTI2:1;                        /*   SSIRTI2    */
             _UDWORD SSII3:1;                          /*   SSII3      */
             _UDWORD SSIRXI3:1;                        /*   SSIRXI3    */
             _UDWORD SSITXI3:1;                        /*   SSITXI3    */
             _UDWORD SSII4:1;                          /*   SSII4      */
             _UDWORD SSIRTI4:1;                        /*   SSIRTI4    */
             _UDWORD SSII5:1;                          /*   SSII5      */
             _UDWORD SSIRXI5:1;                        /*   SSIRXI5    */
             _UDWORD SSITXI5:1;                        /*   SSITXI5    */
             _UDWORD SPDIFI:1;                         /*   SPDIFI     */
             _UDWORD TEI0:1;                           /*   TEI0       */
             _UDWORD RI0:1;                            /*   RI0        */
             _UDWORD TI0:1;                            /*   TI0        */
             } BIT;                                    /*              */
} ICDxxx5;                                             /*              */
typedef union {                                        /* ICDxxx6      */
       _UDWORD LONG;                                   /*  Long Access */
       struct {                                        /*  Bit Access  */
             _UDWORD SPI0:1;                           /*   SPI0       */
             _UDWORD STI0:1;                           /*   STI0       */
             _UDWORD NAKI0:1;                          /*   NAKI0      */
             _UDWORD ALI0:1;                           /*   ALI0       */
             _UDWORD TMOI0:1;                          /*   TMOI0      */
             _UDWORD TEI1:1;                           /*   TEI1       */
             _UDWORD RI1:1;                            /*   RI1        */
             _UDWORD TI1:1;                            /*   TI1        */
             _UDWORD SPI1:1;                           /*   SPI1       */
             _UDWORD STI1:1;                           /*   STI1       */
             _UDWORD NAKI1:1;                          /*   NAKI1      */
             _UDWORD ALI1:1;                           /*   ALI1       */
             _UDWORD TMOI1:1;                          /*   TMOI1      */
             _UDWORD TEI2:1;                           /*   TEI2       */
             _UDWORD RI2:1;                            /*   RI2        */
             _UDWORD TI2:1;                            /*   TI2        */
             _UDWORD SPI2:1;                           /*   SPI2       */
             _UDWORD STI2:1;                           /*   STI2       */
             _UDWORD NAKI2:1;                          /*   NAKI2      */
             _UDWORD ALI2:1;                           /*   ALI2       */
             _UDWORD TMOI2:1;                          /*   TMOI2      */
             _UDWORD TEI3:1;                           /*   TEI3       */
             _UDWORD RI3:1;                            /*   RI3        */
             _UDWORD TI3:1;                            /*   TI3        */
             _UDWORD SPI3:1;                           /*   SPI3       */
             _UDWORD STI3:1;                           /*   STI3       */
             _UDWORD NAKI3:1;                          /*   NAKI3      */
             _UDWORD ALI3:1;                           /*   ALI3       */
             _UDWORD TMOI3:1;                          /*   TMOI3      */
             _UDWORD BRI0:1;                           /*   BRI0       */
             _UDWORD ERI0:1;                           /*   ERI0       */
             _UDWORD RXI0:1;                           /*   RXI0       */
             } BIT;                                    /*              */
} ICDxxx6;                                             /*              */
typedef union {                                        /* ICDxxx7      */
       _UDWORD LONG;                                   /*  Long Access */
       struct {                                        /*  Bit Access  */
             _UDWORD TXI0:1;                           /*   TXI0       */
             _UDWORD BRI1:1;                           /*   BRI1       */
             _UDWORD ERI1:1;                           /*   ERI1       */
             _UDWORD RXI1:1;                           /*   RXI1       */
             _UDWORD TXI1:1;                           /*   TXI1       */
             _UDWORD BRI2:1;                           /*   BRI2       */
             _UDWORD ERI2:1;                           /*   ERI2       */
             _UDWORD RXI2:1;                           /*   RXI2       */
             _UDWORD TXI2:1;                           /*   TXI2       */
             _UDWORD BRI3:1;                           /*   BRI3       */
             _UDWORD ERI3:1;                           /*   ERI3       */
             _UDWORD RXI3:1;                           /*   RXI3       */
             _UDWORD TXI3:1;                           /*   TXI3       */
             _UDWORD BRI4:1;                           /*   BRI4       */
             _UDWORD ERI4:1;                           /*   ERI4       */
             _UDWORD RXI4:1;                           /*   RXI4       */
             _UDWORD TXI4:1;                           /*   TXI4       */
             _UDWORD BRI5:1;                           /*   BRI5       */
             _UDWORD ERI5:1;                           /*   ERI5       */
             _UDWORD RXI5:1;                           /*   RXI5       */
             _UDWORD TXI5:1;                           /*   TXI5       */
             _UDWORD BRI6:1;                           /*   BRI6       */
             _UDWORD ERI6:1;                           /*   ERI6       */
             _UDWORD RXI6:1;                           /*   RXI6       */
             _UDWORD TXI6:1;                           /*   TXI6       */
             _UDWORD BRI7:1;                           /*   BRI7       */
             _UDWORD ERI7:1;                           /*   ERI7       */
             _UDWORD RXI7:1;                           /*   RXI7       */
             _UDWORD TXI7:1;                           /*   TXI7       */
             _UDWORD GERI:1;                           /*   GERI       */
             _UDWORD RFI:1;                            /*   RFI        */
             _UDWORD CFRXI0:1;                         /*   CFRXI0     */
             } BIT;                                    /*              */
} ICDxxx7;                                             /*              */
typedef union {                                        /* ICDxxx8      */
       _UDWORD LONG;                                   /*  Long Access */
       struct {                                        /*  Bit Access  */
             _UDWORD CERI0:1;                          /*   CERI0      */
             _UDWORD CTXI0:1;                          /*   CTXI0      */
             _UDWORD CFRXI1:1;                         /*   CFRXI1     */
             _UDWORD CERI1:1;                          /*   CERI1      */
             _UDWORD CTXI1:1;                          /*   CTXI1      */
             _UDWORD CFRXI2:1;                         /*   CFRXI2     */
             _UDWORD CERI2:1;                          /*   CERI2      */
             _UDWORD CTXI2:1;                          /*   CTXI2      */
             _UDWORD CFRXI3:1;                         /*   CFRXI3     */
             _UDWORD CERI3:1;                          /*   CERI3      */
             _UDWORD CTXI3:1;                          /*   CTXI3      */
             _UDWORD CFRXI4:1;                         /*   CFRXI4     */
             _UDWORD CERI4:1;                          /*   CERI4      */
             _UDWORD CTXI4:1;                          /*   CTXI4      */
             _UDWORD SPEI0:1;                          /*   SPEI0      */
             _UDWORD SPRI0:1;                          /*   SPRI0      */
             _UDWORD SPTI0:1;                          /*   SPTI0      */
             _UDWORD SPEI1:1;                          /*   SPEI1      */
             _UDWORD SPRI1:1;                          /*   SPRI1      */
             _UDWORD SPTI1:1;                          /*   SPTI1      */
             _UDWORD SPEI2:1;                          /*   SPEI2      */
             _UDWORD SPRI2:1;                          /*   SPRI2      */
             _UDWORD SPTI2:1;                          /*   SPTI2      */
             _UDWORD SPEI3:1;                          /*   SPEI3      */
             _UDWORD SPRI3:1;                          /*   SPRI3      */
             _UDWORD SPTI3:1;                          /*   SPTI3      */
             _UDWORD SPEI4:1;                          /*   SPEI4      */
             _UDWORD SPRI4:1;                          /*   SPRI4      */
             _UDWORD SPTI4:1;                          /*   SPTI4      */
             _UDWORD IEBBTD:1;                         /*   IEBBTD     */
             _UDWORD IEBBTERR:1;                       /*   IEBBTERR   */
             _UDWORD IEBBTSTA:1;                       /*   IEBBTSTA   */
             } BIT;                                    /*              */
} ICDxxx8;                                             /*              */
typedef union {                                        /* ICDxxx9      */
       _UDWORD LONG;                                   /*  Long Access */
       struct {                                        /*  Bit Access  */
             _UDWORD IEBBTV:1;                         /*   IEBBTV     */
             _UDWORD ISY:1;                            /*   ISY        */
             _UDWORD IERR:1;                           /*   IERR       */
             _UDWORD ITARG:1;                          /*   ITARG      */
             _UDWORD ISEC:1;                           /*   ISEC       */
             _UDWORD IBUF:1;                           /*   IBUF       */
             _UDWORD IREADY:1;                         /*   IREADY     */
             _UDWORD FLSTE:1;                          /*   FLSTE      */
             _UDWORD FLTENDI:1;                        /*   FLTENDI    */
             _UDWORD FLTREQ0I:1;                       /*   FLTREQ0I   */
             _UDWORD FLTREQ1I:1;                       /*   FLTREQ1I   */
             _UDWORD MMC0:1;                           /*   MMC0       */
             _UDWORD MMC1:1;                           /*   MMC1       */
             _UDWORD MMC2:1;                           /*   MMC2       */
             _UDWORD SDHI0_3:1;                        /*   SDHI0_3    */
             _UDWORD SDHI0_0:1;                        /*   SDHI0_0    */
             _UDWORD SDHI0_1:1;                        /*   SDHI0_1    */
             _UDWORD SDHI1_3:1;                        /*   SDHI1_3    */
             _UDWORD SDHI1_0:1;                        /*   SDHI1_0    */
             _UDWORD SDHI1_1:1;                        /*   SDHI1_1    */
             _UDWORD ARM:1;                            /*   ARM        */
             _UDWORD PRD:1;                            /*   PRD        */
             _UDWORD CUP:1;                            /*   CUP        */
             _UDWORD SCUAI0:1;                         /*   SCUAI0     */
             _UDWORD SCUAI1:1;                         /*   SCUAI1     */
             _UDWORD SCUFDI0:1;                        /*   SCUFDI0    */
             _UDWORD SCUFDI1:1;                        /*   SCUFDI1    */
             _UDWORD SCUFDI2:1;                        /*   SCUFDI2    */
             _UDWORD SCUFDI3:1;                        /*   SCUFDI3    */
             _UDWORD SCUFUI0:1;                        /*   SCUFUI0    */
             _UDWORD SCUFUI1:1;                        /*   SCUFUI1    */
             _UDWORD SCUFUI2:1;                        /*   SCUFUI2    */
             } BIT;                                    /*              */
} ICDxxx9;                                             /*              */
typedef union {                                        /* ICDxxx10     */
       _UDWORD LONG;                                   /*  Long Access */
       struct {                                        /*  Bit Access  */
             _UDWORD SCUFUI3:1;                        /*   SCUFUI3    */
             _UDWORD SCUDVI0:1;                        /*   SCUDVI0    */
             _UDWORD SCUDVI1:1;                        /*   SCUDVI1    */
             _UDWORD SCUDVI2:1;                        /*   SCUDVI2    */
             _UDWORD SCUDVI3:1;                        /*   SCUDVI3    */
             _UDWORD MLBCI:1;                          /*   MLBCI      */
             _UDWORD MLBSI:1;                          /*   MLBSI      */
             _UDWORD DRC0:1;                           /*   DRC0       */
             _UDWORD DRC1:1;                           /*   DRC1       */
             _UDWORD :2;                               /*              */
             _UDWORD LINI0_INT_T:1;                    /*   LINI0_INT_T */
             _UDWORD LINI0_INT_R:1;                    /*   LINI0_INT_R */
             _UDWORD LINI0_INT_S:1;                    /*   LINI0_INT_S */
             _UDWORD LINI0_INT_M:1;                    /*   LINI0_INT_M */
             _UDWORD LINI1_INT_T:1;                    /*   LINI1_INT_T */
             _UDWORD LINI1_INT_R:1;                    /*   LINI1_INT_R */
             _UDWORD LINI1_INT_S:1;                    /*   LINI1_INT_S */
             _UDWORD LINI1_INT_M:1;                    /*   LINI1_INT_M */
             _UDWORD :8;                               /*              */
             _UDWORD ERI0:1;                           /*   ERI0       */
             _UDWORD RXI0:1;                           /*   RXI0       */
             _UDWORD TXI0:1;                           /*   TXI0       */
             _UDWORD TEI0:1;                           /*   TEI0       */
             _UDWORD ERI1:1;                           /*   ERI1       */
             } BIT;                                    /*              */
} ICDxxx10;                                            /*              */
typedef union {                                        /* ICDxxx11     */
       _UDWORD LONG;                                   /*  Long Access */
       struct {                                        /*  Bit Access  */
             _UDWORD RXI1:1;                           /*   RXI1       */
             _UDWORD TXI1:1;                           /*   TXI1       */
             _UDWORD TEI1:1;                           /*   TEI1       */
             _UDWORD :4;                               /*              */
             _UDWORD ETHERI:1;                         /*   ETHERI     */
             _UDWORD :4;                               /*              */
             _UDWORD CEUI:1;                           /*   CEUI       */
             _UDWORD INT_CSIH0TIR:1;                   /*   INT_CSIH0TIR */
             _UDWORD INT_CSIH0TIRE:1;                  /*   INT_CSIH0TIRE */
             _UDWORD INT_CSIH1TIC:1;                   /*   INT_CSIH1TIC */
             _UDWORD INT_CSIH1TIJC:1;                  /*   INT_CSIH1TIJC */
             _UDWORD ECCE10:1;                         /*   ECCE10     */
             _UDWORD ECCE20:1;                         /*   ECCE20     */
             _UDWORD ECCOVF0:1;                        /*   ECCOVF0    */
             _UDWORD ECCE11:1;                         /*   ECCE11     */
             _UDWORD ECCE21:1;                         /*   ECCE21     */
             _UDWORD ECCOVF1:1;                        /*   ECCOVF1    */
             _UDWORD ECCE12:1;                         /*   ECCE12     */
             _UDWORD ECCE22:1;                         /*   ECCE22     */
             _UDWORD ECCOVF2:1;                        /*   ECCOVF2    */
             _UDWORD ECCE13:1;                         /*   ECCE13     */
             _UDWORD ECCE23:1;                         /*   ECCE23     */
             _UDWORD ECCOVF3:1;                        /*   ECCOVF3    */
             _UDWORD H2XMLB_ERRINT:1;                  /*   H2XMLB_ERRINT */
             _UDWORD H2XIC1_ERRINT:1;                  /*   H2XIC1_ERRINT */
             _UDWORD X2HPERI1_ERRINT:1;                /*   X2HPERI1_ERRINT */
             } BIT;                                    /*              */
} ICDxxx11;                                            /*              */
typedef union {                                        /* ICDxxx12     */
       _UDWORD LONG;                                   /*  Long Access */
       struct {                                        /*  Bit Access  */
             _UDWORD X2HPERI2_ERRINT:1;                /*   X2HPERI2_ERRINT */
             _UDWORD X2HPERI34_ERRINT:1;               /*   X2HPERI34_ERRINT */
             _UDWORD X2HPERI5_ERRINT:1;                /*   X2HPERI5_ERRINT */
             _UDWORD X2HPERI67_ERRINT:1;               /*   X2HPERI67_ERRINT */
             _UDWORD X2HDBGR_ERRINT:1;                 /*   X2HDBGR_ERRINT */
             _UDWORD PRRI:1;                           /*   PRRI       */
             _UDWORD IFEI0:1;                          /*   IFEI0      */
             _UDWORD OFFI0:1;                          /*   OFFI0      */
             _UDWORD PFVEI0:1;                         /*   PFVEI0     */
             _UDWORD IFEI1:1;                          /*   IFEI1      */
             _UDWORD OFFI1:1;                          /*   OFFI1      */
             _UDWORD PFVEI1:1;                         /*   PFVEI1     */
             _UDWORD :20;                              /*              */
             } BIT;                                    /*              */
} ICDxxx12;                                            /*              */
typedef union {                                        /* ICDxxx13     */
       _UDWORD LONG;                                   /*  Long Access */
       struct {                                        /*  Bit Access  */
             _UDWORD TINT0:1;                          /*   TINT0      */
             _UDWORD TINT1:1;                          /*   TINT1      */
             _UDWORD TINT2:1;                          /*   TINT2      */
             _UDWORD TINT3:1;                          /*   TINT3      */
             _UDWORD TINT4:1;                          /*   TINT4      */
             _UDWORD TINT5:1;                          /*   TINT5      */
             _UDWORD TINT6:1;                          /*   TINT6      */
             _UDWORD TINT7:1;                          /*   TINT7      */
             _UDWORD TINT8:1;                          /*   TINT8      */
             _UDWORD TINT9:1;                          /*   TINT9      */
             _UDWORD TINT10:1;                         /*   TINT10     */
             _UDWORD TINT11:1;                         /*   TINT11     */
             _UDWORD TINT12:1;                         /*   TINT12     */
             _UDWORD TINT13:1;                         /*   TINT13     */
             _UDWORD TINT14:1;                         /*   TINT14     */
             _UDWORD TINT15:1;                         /*   TINT15     */
             _UDWORD TINT16:1;                         /*   TINT16     */
             _UDWORD TINT17:1;                         /*   TINT17     */
             _UDWORD TINT18:1;                         /*   TINT18     */
             _UDWORD TINT19:1;                         /*   TINT19     */
             _UDWORD TINT20:1;                         /*   TINT20     */
             _UDWORD TINT21:1;                         /*   TINT21     */
             _UDWORD TINT22:1;                         /*   TINT22     */
             _UDWORD TINT23:1;                         /*   TINT23     */
             _UDWORD TINT24:1;                         /*   TINT24     */
             _UDWORD TINT25:1;                         /*   TINT25     */
             _UDWORD TINT26:1;                         /*   TINT26     */
             _UDWORD TINT27:1;                         /*   TINT27     */
             _UDWORD TINT28:1;                         /*   TINT28     */
             _UDWORD TINT29:1;                         /*   TINT29     */
             _UDWORD TINT30:1;                         /*   TINT30     */
             _UDWORD TINT31:1;                         /*   TINT31     */
             } BIT;                                    /*              */
} ICDxxx13;                                            /*              */
typedef union {                                        /* ICDxxx14     */
       _UDWORD LONG;                                   /*  Long Access */
       struct {                                        /*  Bit Access  */
             _UDWORD TINT32:1;                         /*   TINT32     */
             _UDWORD TINT33:1;                         /*   TINT33     */
             _UDWORD TINT34:1;                         /*   TINT34     */
             _UDWORD TINT35:1;                         /*   TINT35     */
             _UDWORD TINT36:1;                         /*   TINT36     */
             _UDWORD TINT37:1;                         /*   TINT37     */
             _UDWORD TINT38:1;                         /*   TINT38     */
             _UDWORD TINT39:1;                         /*   TINT39     */
             _UDWORD TINT40:1;                         /*   TINT40     */
             _UDWORD TINT41:1;                         /*   TINT41     */
             _UDWORD TINT42:1;                         /*   TINT42     */
             _UDWORD TINT43:1;                         /*   TINT43     */
             _UDWORD TINT44:1;                         /*   TINT44     */
             _UDWORD TINT45:1;                         /*   TINT45     */
             _UDWORD TINT46:1;                         /*   TINT46     */
             _UDWORD TINT47:1;                         /*   TINT47     */
             _UDWORD TINT48:1;                         /*   TINT48     */
             _UDWORD TINT49:1;                         /*   TINT49     */
             _UDWORD TINT50:1;                         /*   TINT50     */
             _UDWORD TINT51:1;                         /*   TINT51     */
             _UDWORD TINT52:1;                         /*   TINT52     */
             _UDWORD TINT53:1;                         /*   TINT53     */
             _UDWORD TINT54:1;                         /*   TINT54     */
             _UDWORD TINT55:1;                         /*   TINT55     */
             _UDWORD TINT56:1;                         /*   TINT56     */
             _UDWORD TINT57:1;                         /*   TINT57     */
             _UDWORD TINT58:1;                         /*   TINT58     */
             _UDWORD TINT59:1;                         /*   TINT59     */
             _UDWORD TINT60:1;                         /*   TINT60     */
             _UDWORD TINT61:1;                         /*   TINT61     */
             _UDWORD TINT62:1;                         /*   TINT62     */
             _UDWORD TINT63:1;                         /*   TINT63     */
             } BIT;                                    /*              */
} ICDxxx14;                                            /*              */
typedef union {                                        /* ICDxxx15     */
       _UDWORD LONG;                                   /*  Long Access */
       struct {                                        /*  Bit Access  */
             _UDWORD TINT64:1;                         /*   TINT64     */
             _UDWORD TINT65:1;                         /*   TINT65     */
             _UDWORD TINT66:1;                         /*   TINT66     */
             _UDWORD TINT67:1;                         /*   TINT67     */
             _UDWORD TINT68:1;                         /*   TINT68     */
             _UDWORD TINT69:1;                         /*   TINT69     */
             _UDWORD TINT70:1;                         /*   TINT70     */
             _UDWORD TINT71:1;                         /*   TINT71     */
             _UDWORD TINT72:1;                         /*   TINT72     */
             _UDWORD TINT73:1;                         /*   TINT73     */
             _UDWORD TINT74:1;                         /*   TINT74     */
             _UDWORD TINT75:1;                         /*   TINT75     */
             _UDWORD TINT76:1;                         /*   TINT76     */
             _UDWORD TINT77:1;                         /*   TINT77     */
             _UDWORD TINT78:1;                         /*   TINT78     */
             _UDWORD TINT79:1;                         /*   TINT79     */
             _UDWORD TINT80:1;                         /*   TINT80     */
             _UDWORD TINT81:1;                         /*   TINT81     */
             _UDWORD TINT82:1;                         /*   TINT82     */
             _UDWORD TINT83:1;                         /*   TINT83     */
             _UDWORD TINT84:1;                         /*   TINT84     */
             _UDWORD TINT85:1;                         /*   TINT85     */
             _UDWORD TINT86:1;                         /*   TINT86     */
             _UDWORD TINT87:1;                         /*   TINT87     */
             _UDWORD TINT88:1;                         /*   TINT88     */
             _UDWORD TINT89:1;                         /*   TINT89     */
             _UDWORD TINT90:1;                         /*   TINT90     */
             _UDWORD TINT91:1;                         /*   TINT91     */
             _UDWORD TINT92:1;                         /*   TINT92     */
             _UDWORD TINT93:1;                         /*   TINT93     */
             _UDWORD TINT94:1;                         /*   TINT94     */
             _UDWORD TINT95:1;                         /*   TINT95     */
             } BIT;                                    /*              */
} ICDxxx15;                                            /*              */
typedef union {                                        /* ICDxxx16     */
       _UDWORD LONG;                                   /*  Long Access */
       struct {                                        /*  Bit Access  */
             _UDWORD TINT96:1;                         /*   TINT96     */
             _UDWORD TINT97:1;                         /*   TINT97     */
             _UDWORD TINT98:1;                         /*   TINT98     */
             _UDWORD TINT99:1;                         /*   TINT99     */
             _UDWORD TINT100:1;                        /*   TINT100    */
             _UDWORD TINT101:1;                        /*   TINT101    */
             _UDWORD TINT102:1;                        /*   TINT102    */
             _UDWORD TINT103:1;                        /*   TINT103    */
             _UDWORD TINT104:1;                        /*   TINT104    */
             _UDWORD TINT105:1;                        /*   TINT105    */
             _UDWORD TINT106:1;                        /*   TINT106    */
             _UDWORD TINT107:1;                        /*   TINT107    */
             _UDWORD TINT108:1;                        /*   TINT108    */
             _UDWORD TINT109:1;                        /*   TINT109    */
             _UDWORD TINT110:1;                        /*   TINT110    */
             _UDWORD TINT111:1;                        /*   TINT111    */
             _UDWORD TINT112:1;                        /*   TINT112    */
             _UDWORD TINT113:1;                        /*   TINT113    */
             _UDWORD TINT114:1;                        /*   TINT114    */
             _UDWORD TINT115:1;                        /*   TINT115    */
             _UDWORD TINT116:1;                        /*   TINT116    */
             _UDWORD TINT117:1;                        /*   TINT117    */
             _UDWORD TINT118:1;                        /*   TINT118    */
             _UDWORD TINT119:1;                        /*   TINT119    */
             _UDWORD TINT120:1;                        /*   TINT120    */
             _UDWORD TINT121:1;                        /*   TINT121    */
             _UDWORD TINT122:1;                        /*   TINT122    */
             _UDWORD TINT123:1;                        /*   TINT123    */
             _UDWORD TINT124:1;                        /*   TINT124    */
             _UDWORD TINT125:1;                        /*   TINT125    */
             _UDWORD TINT126:1;                        /*   TINT126    */
             _UDWORD TINT127:1;                        /*   TINT127    */
             } BIT;                                    /*              */
} ICDxxx16;                                            /*              */
typedef union {                                        /* ICDxxx17     */
       _UDWORD LONG;                                   /*  Long Access */
       struct {                                        /*  Bit Access  */
             _UDWORD TINT128:1;                        /*   TINT128    */
             _UDWORD TINT129:1;                        /*   TINT129    */
             _UDWORD TINT130:1;                        /*   TINT130    */
             _UDWORD TINT131:1;                        /*   TINT131    */
             _UDWORD TINT132:1;                        /*   TINT132    */
             _UDWORD TINT133:1;                        /*   TINT133    */
             _UDWORD TINT134:1;                        /*   TINT134    */
             _UDWORD TINT135:1;                        /*   TINT135    */
             _UDWORD TINT136:1;                        /*   TINT136    */
             _UDWORD TINT137:1;                        /*   TINT137    */
             _UDWORD TINT138:1;                        /*   TINT138    */
             _UDWORD TINT139:1;                        /*   TINT139    */
             _UDWORD TINT140:1;                        /*   TINT140    */
             _UDWORD TINT141:1;                        /*   TINT141    */
             _UDWORD TINT142:1;                        /*   TINT142    */
             _UDWORD TINT143:1;                        /*   TINT143    */
             _UDWORD TINT144:1;                        /*   TINT144    */
             _UDWORD TINT145:1;                        /*   TINT145    */
             _UDWORD TINT146:1;                        /*   TINT146    */
             _UDWORD TINT147:1;                        /*   TINT147    */
             _UDWORD TINT148:1;                        /*   TINT148    */
             _UDWORD TINT149:1;                        /*   TINT149    */
             _UDWORD TINT150:1;                        /*   TINT150    */
             _UDWORD TINT151:1;                        /*   TINT151    */
             _UDWORD TINT152:1;                        /*   TINT152    */
             _UDWORD TINT153:1;                        /*   TINT153    */
             _UDWORD TINT154:1;                        /*   TINT154    */
             _UDWORD TINT155:1;                        /*   TINT155    */
             _UDWORD TINT156:1;                        /*   TINT156    */
             _UDWORD TINT157:1;                        /*   TINT157    */
             _UDWORD TINT158:1;                        /*   TINT158    */
             _UDWORD TINT159:1;                        /*   TINT159    */
             } BIT;                                    /*              */
} ICDxxx17;                                            /*              */
typedef union {                                        /* ICDxxx18     */
       _UDWORD LONG;                                   /*  Long Access */
       struct {                                        /*  Bit Access  */
             _UDWORD TINT160:1;                        /*   TINT160    */
             _UDWORD TINT161:1;                        /*   TINT161    */
             _UDWORD TINT162:1;                        /*   TINT162    */
             _UDWORD :29;                              /*              */
             } BIT;                                    /*              */
} ICDxxx18;                                            /*              */


struct st_intc {                                       /* struct INTC  */
       union {                                         /* ICDDCR       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD Enable:1;                  /*   Enable     */
                    _UDWORD :31;                       /*              */
                    } BIT;                             /*              */
             } ICDDCR;                                 /*              */
       union {                                         /* ICDICTR      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD ITLinesNumber:5;           /*   ITLinesNumber */
                    _UDWORD CPUNumber:3;               /*   CPUNumber  */
                    _UDWORD :2;                        /*              */
                    _UDWORD SecurityExtn:1;            /*   SecurityExtn */
                    _UDWORD LSPI:5;                    /*   LSPI       */
                    _UDWORD :16;                       /*              */
                    } BIT;                             /*              */
             } ICDICTR;                                /*              */
       union {                                         /* ICDIIDR      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD Implementer:12;            /*   Implementer */
                    _UDWORD Revision:4;                /*   Revision   */
                    _UDWORD Variant:4;                 /*   Variant    */
                    _UDWORD :4;                        /*              */
                    _UDWORD ProductID:8;               /*   ProductID  */
                    } BIT;                             /*              */
             } ICDIIDR;                                /*              */
       _UBYTE wk0[116];                                /*              */
       union {                                         /* ICDISR       */
             _UDWORD LONG[19];                         /*  Long Access */
             struct {                                  /*  ICDISRn     */
                    ICDxxx0  ICDISR0;                  /* ICDISR0      */
                    ICDxxx1  ICDISR1;                  /* ICDISR1      */
                    ICDxxx2  ICDISR2;                  /* ICDISR2      */
                    ICDxxx3  ICDISR3;                  /* ICDISR3      */
                    ICDxxx4  ICDISR4;                  /* ICDISR4      */
                    ICDxxx5  ICDISR5;                  /* ICDISR5      */
                    ICDxxx6  ICDISR6;                  /* ICDISR6      */
                    ICDxxx7  ICDISR7;                  /* ICDISR7      */
                    ICDxxx8  ICDISR8;                  /* ICDISR8      */
                    ICDxxx9  ICDISR9;                  /* ICDISR9      */
                    ICDxxx10 ICDISR10;                 /* ICDISR10     */
                    ICDxxx11 ICDISR11;                 /* ICDISR11     */
                    ICDxxx12 ICDISR12;                 /* ICDISR12     */
                    ICDxxx13 ICDISR13;                 /* ICDISR13     */
                    ICDxxx14 ICDISR14;                 /* ICDISR14     */
                    ICDxxx15 ICDISR15;                 /* ICDISR15     */
                    ICDxxx16 ICDISR16;                 /* ICDISR16     */
                    ICDxxx17 ICDISR17;                 /* ICDISR17     */
                    ICDxxx18 ICDISR18;                 /* ICDISR18     */
                    } n;                               /*              */
             } ICDISR;                                 /*              */
       _UBYTE wk1[52];                                 /*              */
       union {                                         /* ICDISER      */
             _UDWORD LONG[19];                         /*  Long Access */
             struct {                                  /*  ICDISERn    */
                    ICDxxx0  ICDISER0;                 /* ICDISER0     */
                    ICDxxx1  ICDISER1;                 /* ICDISER1     */
                    ICDxxx2  ICDISER2;                 /* ICDISER2     */
                    ICDxxx3  ICDISER3;                 /* ICDISER3     */
                    ICDxxx4  ICDISER4;                 /* ICDISER4     */
                    ICDxxx5  ICDISER5;                 /* ICDISER5     */
                    ICDxxx6  ICDISER6;                 /* ICDISER6     */
                    ICDxxx7  ICDISER7;                 /* ICDISER7     */
                    ICDxxx8  ICDISER8;                 /* ICDISER8     */
                    ICDxxx9  ICDISER9;                 /* ICDISER9     */
                    ICDxxx10 ICDISER10;                /* ICDISER10    */
                    ICDxxx11 ICDISER11;                /* ICDISER11    */
                    ICDxxx12 ICDISER12;                /* ICDISER12    */
                    ICDxxx13 ICDISER13;                /* ICDISER13    */
                    ICDxxx14 ICDISER14;                /* ICDISER14    */
                    ICDxxx15 ICDISER15;                /* ICDISER15    */
                    ICDxxx16 ICDISER16;                /* ICDISER16    */
                    ICDxxx17 ICDISER17;                /* ICDISER17    */
                    ICDxxx18 ICDISER18;                /* ICDISER18    */
                    } n;                               /*              */
             } ICDISER;                                /*              */
       _UBYTE wk2[52];                                 /*              */
       union {                                         /* ICDICER      */
             _UDWORD LONG[19];                         /*  Long Access */
             struct {                                  /*  ICDICERn    */
                    ICDxxx0  ICDICER0;                 /* ICDICER0     */
                    ICDxxx1  ICDICER1;                 /* ICDICER1     */
                    ICDxxx2  ICDICER2;                 /* ICDICER2     */
                    ICDxxx3  ICDICER3;                 /* ICDICER3     */
                    ICDxxx4  ICDICER4;                 /* ICDICER4     */
                    ICDxxx5  ICDICER5;                 /* ICDICER5     */
                    ICDxxx6  ICDICER6;                 /* ICDICER6     */
                    ICDxxx7  ICDICER7;                 /* ICDICER7     */
                    ICDxxx8  ICDICER8;                 /* ICDICER8     */
                    ICDxxx9  ICDICER9;                 /* ICDICER9     */
                    ICDxxx10 ICDICER10;                /* ICDICER10    */
                    ICDxxx11 ICDICER11;                /* ICDICER11    */
                    ICDxxx12 ICDICER12;                /* ICDICER12    */
                    ICDxxx13 ICDICER13;                /* ICDICER13    */
                    ICDxxx14 ICDICER14;                /* ICDICER14    */
                    ICDxxx15 ICDICER15;                /* ICDICER15    */
                    ICDxxx16 ICDICER16;                /* ICDICER16    */
                    ICDxxx17 ICDICER17;                /* ICDICER17    */
                    ICDxxx18 ICDICER18;                /* ICDICER18    */
                    } n;                               /*              */
             } ICDICER;                                /*              */
       _UBYTE wk3[52];                                 /*              */
       union {                                         /* ICDISPR      */
             _UDWORD LONG[19];                         /*  Long Access */
             struct {                                  /*  ICDISPRn    */
                    ICDxxx0  ICDISPR0;                 /* ICDISPR0     */
                    ICDxxx1  ICDISPR1;                 /* ICDISPR1     */
                    ICDxxx2  ICDISPR2;                 /* ICDISPR2     */
                    ICDxxx3  ICDISPR3;                 /* ICDISPR3     */
                    ICDxxx4  ICDISPR4;                 /* ICDISPR4     */
                    ICDxxx5  ICDISPR5;                 /* ICDISPR5     */
                    ICDxxx6  ICDISPR6;                 /* ICDISPR6     */
                    ICDxxx7  ICDISPR7;                 /* ICDISPR7     */
                    ICDxxx8  ICDISPR8;                 /* ICDISPR8     */
                    ICDxxx9  ICDISPR9;                 /* ICDISPR9     */
                    ICDxxx10 ICDISPR10;                /* ICDISPR10    */
                    ICDxxx11 ICDISPR11;                /* ICDISPR11    */
                    ICDxxx12 ICDISPR12;                /* ICDISPR12    */
                    ICDxxx13 ICDISPR13;                /* ICDISPR13    */
                    ICDxxx14 ICDISPR14;                /* ICDISPR14    */
                    ICDxxx15 ICDISPR15;                /* ICDISPR15    */
                    ICDxxx16 ICDISPR16;                /* ICDISPR16    */
                    ICDxxx17 ICDISPR17;                /* ICDISPR17    */
                    ICDxxx18 ICDISPR18;                /* ICDISPR18    */
                    } n;                               /*              */
             } ICDISPR;                                /*              */
       _UBYTE wk4[52];                                 /*              */
       union {                                         /* ICDICPR      */
             _UDWORD LONG[19];                         /*  Long Access */
             struct {                                  /*  ICDICPRn    */
                    ICDxxx0  ICDICPR0;                 /* ICDICPR0     */
                    ICDxxx1  ICDICPR1;                 /* ICDICPR1     */
                    ICDxxx2  ICDICPR2;                 /* ICDICPR2     */
                    ICDxxx3  ICDICPR3;                 /* ICDICPR3     */
                    ICDxxx4  ICDICPR4;                 /* ICDICPR4     */
                    ICDxxx5  ICDICPR5;                 /* ICDICPR5     */
                    ICDxxx6  ICDICPR6;                 /* ICDICPR6     */
                    ICDxxx7  ICDICPR7;                 /* ICDICPR7     */
                    ICDxxx8  ICDICPR8;                 /* ICDICPR8     */
                    ICDxxx9  ICDICPR9;                 /* ICDICPR9     */
                    ICDxxx10 ICDICPR10;                /* ICDICPR10    */
                    ICDxxx11 ICDICPR11;                /* ICDICPR11    */
                    ICDxxx12 ICDICPR12;                /* ICDICPR12    */
                    ICDxxx13 ICDICPR13;                /* ICDICPR13    */
                    ICDxxx14 ICDICPR14;                /* ICDICPR14    */
                    ICDxxx15 ICDICPR15;                /* ICDICPR15    */
                    ICDxxx16 ICDICPR16;                /* ICDICPR16    */
                    ICDxxx17 ICDICPR17;                /* ICDICPR17    */
                    ICDxxx18 ICDICPR18;                /* ICDICPR18    */
                    } n;                               /*              */
             } ICDICPR;                                /*              */
       _UBYTE wk5[52];                                 /*              */
       union {                                         /* ICDABR       */
             _UDWORD LONG[19];                         /*  Long Access */
             struct {                                  /*  ICDABRn     */
                    ICDxxx0  ICDABR0;                  /* ICDABR0      */
                    ICDxxx1  ICDABR1;                  /* ICDABR1      */
                    ICDxxx2  ICDABR2;                  /* ICDABR2      */
                    ICDxxx3  ICDABR3;                  /* ICDABR3      */
                    ICDxxx4  ICDABR4;                  /* ICDABR4      */
                    ICDxxx5  ICDABR5;                  /* ICDABR5      */
                    ICDxxx6  ICDABR6;                  /* ICDABR6      */
                    ICDxxx7  ICDABR7;                  /* ICDABR7      */
                    ICDxxx8  ICDABR8;                  /* ICDABR8      */
                    ICDxxx9  ICDABR9;                  /* ICDABR9      */
                    ICDxxx10 ICDABR10;                 /* ICDABR10     */
                    ICDxxx11 ICDABR11;                 /* ICDABR11     */
                    ICDxxx12 ICDABR12;                 /* ICDABR12     */
                    ICDxxx13 ICDABR13;                 /* ICDABR13     */
                    ICDxxx14 ICDABR14;                 /* ICDABR14     */
                    ICDxxx15 ICDABR15;                 /* ICDABR15     */
                    ICDxxx16 ICDABR16;                 /* ICDABR16     */
                    ICDxxx17 ICDABR17;                 /* ICDABR17     */
                    ICDxxx18 ICDABR18;                 /* ICDABR18     */
                    } n;                               /*              */
             } ICDABR;                                 /*              */
       _UBYTE wk6[180];                                /*              */
       union {                                         /* ICDIPR0      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SW0:8;                     /*   SW0        */
                    _UDWORD SW1:8;                     /*   SW1        */
                    _UDWORD SW2:8;                     /*   SW2        */
                    _UDWORD SW3:8;                     /*   SW3        */
                    } BIT;                             /*              */
             } ICDIPR0;                                /*              */
       union {                                         /* ICDIPR1      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SW4:8;                     /*   SW4        */
                    _UDWORD SW5:8;                     /*   SW5        */
                    _UDWORD SW6:8;                     /*   SW6        */
                    _UDWORD SW7:8;                     /*   SW7        */
                    } BIT;                             /*              */
             } ICDIPR1;                                /*              */
       union {                                         /* ICDIPR2      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SW8:8;                     /*   SW8        */
                    _UDWORD SW9:8;                     /*   SW9        */
                    _UDWORD SW10:8;                    /*   SW10       */
                    _UDWORD SW11:8;                    /*   SW11       */
                    } BIT;                             /*              */
             } ICDIPR2;                                /*              */
       union {                                         /* ICDIPR3      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SW12:8;                    /*   SW12       */
                    _UDWORD SW13:8;                    /*   SW13       */
                    _UDWORD SW14:8;                    /*   SW14       */
                    _UDWORD SW15:8;                    /*   SW15       */
                    } BIT;                             /*              */
             } ICDIPR3;                                /*              */
       union {                                         /* ICDIPR4      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD PMUIRQ0:8;                 /*   PMUIRQ0    */
                    _UDWORD COMMRX0:8;                 /*   COMMRX0    */
                    _UDWORD COMMTX0:8;                 /*   COMMTX0    */
                    _UDWORD CTIIRQ0:8;                 /*   CTIIRQ0    */
                    } BIT;                             /*              */
             } ICDIPR4;                                /*              */
       _UBYTE wk7[12];                                 /*              */
       union {                                         /* ICDIPR8      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD IRQ0:8;                    /*   IRQ0       */
                    _UDWORD IRQ1:8;                    /*   IRQ1       */
                    _UDWORD IRQ2:8;                    /*   IRQ2       */
                    _UDWORD IRQ3:8;                    /*   IRQ3       */
                    } BIT;                             /*              */
             } ICDIPR8;                                /*              */
       union {                                         /* ICDIPR9      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD IRQ4:8;                    /*   IRQ4       */
                    _UDWORD IRQ5:8;                    /*   IRQ5       */
                    _UDWORD IRQ6:8;                    /*   IRQ6       */
                    _UDWORD IRQ7:8;                    /*   IRQ7       */
                    } BIT;                             /*              */
             } ICDIPR9;                                /*              */
       union {                                         /* ICDIPR10     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD PL310ERR:8;                /*   PL310ERR   */
                    _UDWORD DMAINT0:8;                 /*   DMAINT0    */
                    _UDWORD DMAINT1:8;                 /*   DMAINT1    */
                    _UDWORD DMAINT2:8;                 /*   DMAINT2    */
                    } BIT;                             /*              */
             } ICDIPR10;                               /*              */
       union {                                         /* ICDIPR11     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD DMAINT3:8;                 /*   DMAINT3    */
                    _UDWORD DMAINT4:8;                 /*   DMAINT4    */
                    _UDWORD DMAINT5:8;                 /*   DMAINT5    */
                    _UDWORD DMAINT6:8;                 /*   DMAINT6    */
                    } BIT;                             /*              */
             } ICDIPR11;                               /*              */
       union {                                         /* ICDIPR12     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD DMAINT7:8;                 /*   DMAINT7    */
                    _UDWORD DMAINT8:8;                 /*   DMAINT8    */
                    _UDWORD DMAINT9:8;                 /*   DMAINT9    */
                    _UDWORD DMAINT10:8;                /*   DMAINT10   */
                    } BIT;                             /*              */
             } ICDIPR12;                               /*              */
       union {                                         /* ICDIPR13     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD DMAINT11:8;                /*   DMAINT11   */
                    _UDWORD DMAINT12:8;                /*   DMAINT12   */
                    _UDWORD DMAINT13:8;                /*   DMAINT13   */
                    _UDWORD DMAINT14:8;                /*   DMAINT14   */
                    } BIT;                             /*              */
             } ICDIPR13;                               /*              */
       union {                                         /* ICDIPR14     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD DMAINT15:8;                /*   DMAINT15   */
                    _UDWORD DMAERR:8;                  /*   DMAERR     */
                    _UDWORD :16;                       /*              */
                    } BIT;                             /*              */
             } ICDIPR14;                               /*              */
       _UBYTE wk8[12];                                 /*              */
       union {                                         /* ICDIPR18     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :8;                        /*              */
                    _UDWORD USBI0:8;                   /*   USBI0      */
                    _UDWORD USBI1:8;                   /*   USBI1      */
                    _UDWORD S0_VI_VSYNC0:8;            /*   S0_VI_VSYNC0 */
                    } BIT;                             /*              */
             } ICDIPR18;                               /*              */
       union {                                         /* ICDIPR19     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD S0_LO_VSYNC0:8;            /*   S0_LO_VSYNC0 */
                    _UDWORD S0_VSYNCERR0:8;            /*   S0_VSYNCERR0 */
                    _UDWORD GR3_VLINE0:8;              /*   GR3_VLINE0 */
                    _UDWORD S0_VFIELD0:8;              /*   S0_VFIELD0 */
                    } BIT;                             /*              */
             } ICDIPR19;                               /*              */
       union {                                         /* ICDIPR20     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD IV1_VBUFERR0:8;            /*   IV1_VBUFERR0 */
                    _UDWORD IV3_VBUFERR0:8;            /*   IV3_VBUFERR0 */
                    _UDWORD IV5_VBUFERR0:8;            /*   IV5_VBUFERR0 */
                    _UDWORD IV6_VBUFERR0:8;            /*   IV6_VBUFERR0 */
                    } BIT;                             /*              */
             } ICDIPR20;                               /*              */
       union {                                         /* ICDIPR21     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD S0_WLINE0:8;               /*   S0_WLINE0  */
                    _UDWORD S1_VI_VSYNC0:8;            /*   S1_VI_VSYNC0 */
                    _UDWORD S1_LO_VSYNC0:8;            /*   S1_LO_VSYNC0 */
                    _UDWORD S1_VSYNCERR0:8;            /*   S1_VSYNCERR0 */
                    } BIT;                             /*              */
             } ICDIPR21;                               /*              */
       union {                                         /* ICDIPR22     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD S1_VFIELD0:8;              /*   S1_VFIELD0 */
                    _UDWORD IV2_VBUFERR0:8;            /*   IV2_VBUFERR0 */
                    _UDWORD IV4_VBUFERR0:8;            /*   IV4_VBUFERR0 */
                    _UDWORD S1_WLINE0:8;               /*   S1_WLINE0  */
                    } BIT;                             /*              */
             } ICDIPR22;                               /*              */
       union {                                         /* ICDIPR23     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD OIR_VI_VSYNC0:8;           /*   OIR_VI_VSYNC0 */
                    _UDWORD OIR_LO_VSYNC0:8;           /*   OIR_LO_VSYNC0 */
                    _UDWORD OIR_VSYNCERR0:8;           /*   OIR_VSYNCERR0 */
                    _UDWORD OIR_VFIELD0:8;             /*   OIR_VFIELD0 */
                    } BIT;                             /*              */
             } ICDIPR23;                               /*              */
       union {                                         /* ICDIPR24     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD IV7_VBUFERR0:8;            /*   IV7_VBUFERR0 */
                    _UDWORD IV8_VBUFERR0:8;            /*   IV8_VBUFERR0 */
                    _UDWORD OIR_WLINE0:8;              /*   OIR_WLINE0 */
                    _UDWORD S0_VI_VSYNC1:8;            /*   S0_VI_VSYNC1 */
                    } BIT;                             /*              */
             } ICDIPR24;                               /*              */
       union {                                         /* ICDIPR25     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD S0_LO_VSYNC1:8;            /*   S0_LO_VSYNC1 */
                    _UDWORD S0_VSYNCERR1:8;            /*   S0_VSYNCERR1 */
                    _UDWORD GR3_VLINE1:8;              /*   GR3_VLINE1 */
                    _UDWORD S0_VFIELD1:8;              /*   S0_VFIELD1 */
                    } BIT;                             /*              */
             } ICDIPR25;                               /*              */
       union {                                         /* ICDIPR26     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD IV1_VBUFERR1:8;            /*   IV1_VBUFERR1 */
                    _UDWORD IV3_VBUFERR1:8;            /*   IV3_VBUFERR1 */
                    _UDWORD IV5_VBUFERR1:8;            /*   IV5_VBUFERR1 */
                    _UDWORD IV6_VBUFERR1:8;            /*   IV6_VBUFERR1 */
                    } BIT;                             /*              */
             } ICDIPR26;                               /*              */
       union {                                         /* ICDIPR27     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD S0_WLINE1:8;               /*   S0_WLINE1  */
                    _UDWORD S1_VI_VSYNC1:8;            /*   S1_VI_VSYNC1 */
                    _UDWORD S1_LO_VSYNC1:8;            /*   S1_LO_VSYNC1 */
                    _UDWORD S1_VSYNCERR1:8;            /*   S1_VSYNCERR1 */
                    } BIT;                             /*              */
             } ICDIPR27;                               /*              */
       union {                                         /* ICDIPR28     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD S1_VFIELD1:8;              /*   S1_VFIELD1 */
                    _UDWORD IV2_VBUFERR1:8;            /*   IV2_VBUFERR1 */
                    _UDWORD IV4_VBUFERR1:8;            /*   IV4_VBUFERR1 */
                    _UDWORD S1_WLINE1:8;               /*   S1_WLINE1  */
                    } BIT;                             /*              */
             } ICDIPR28;                               /*              */
       union {                                         /* ICDIPR29     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD OIR_VI_VSYNC1:8;           /*   OIR_VI_VSYNC1 */
                    _UDWORD OIR_LO_VSYNC1:8;           /*   OIR_LO_VSYNC1 */
                    _UDWORD OIR_VLINE1:8;              /*   OIR_VLINE1 */
                    _UDWORD OIR_VFIELD1:8;             /*   OIR_VFIELD1 */
                    } BIT;                             /*              */
             } ICDIPR29;                               /*              */
       union {                                         /* ICDIPR30     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD IV7_VBUFERR1:8;            /*   IV7_VBUFERR1 */
                    _UDWORD IV8_VBUFERR1:8;            /*   IV8_VBUFERR1 */
                    _UDWORD OIR_WLINE1:8;              /*   OIR_WLINE1 */
                    _UDWORD IMRDI:8;                   /*   IMRDI      */
                    } BIT;                             /*              */
             } ICDIPR30;                               /*              */
       union {                                         /* ICDIPR31     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD IMR2I0:8;                  /*   IMR2I0     */
                    _UDWORD IMR2I1:8;                  /*   IMR2I1     */
                    _UDWORD JEDI:8;                    /*   JEDI       */
                    _UDWORD JDTI:8;                    /*   JDTI       */
                    } BIT;                             /*              */
             } ICDIPR31;                               /*              */
       union {                                         /* ICDIPR32     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CMP0:8;                    /*   CMP0       */
                    _UDWORD CMP1:8;                    /*   CMP1       */
                    _UDWORD INT0:8;                    /*   INT0       */
                    _UDWORD INT1:8;                    /*   INT1       */
                    } BIT;                             /*              */
             } ICDIPR32;                               /*              */
       union {                                         /* ICDIPR33     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD INT2:8;                    /*   INT2       */
                    _UDWORD INT3:8;                    /*   INT3       */
                    _UDWORD OSTMI0:8;                  /*   OSTMI0     */
                    _UDWORD OSTMI1:8;                  /*   OSTMI1     */
                    } BIT;                             /*              */
             } ICDIPR33;                               /*              */
       union {                                         /* ICDIPR34     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CMI:8;                     /*   CMI        */
                    _UDWORD WTOUT:8;                   /*   WTOUT      */
                    _UDWORD ITI:8;                     /*   ITI        */
                    _UDWORD TGI0A:8;                   /*   TGI0A      */
                    } BIT;                             /*              */
             } ICDIPR34;                               /*              */
       union {                                         /* ICDIPR35     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TGI0B:8;                   /*   TGI0B      */
                    _UDWORD TGI0C:8;                   /*   TGI0C      */
                    _UDWORD TGI0D:8;                   /*   TGI0D      */
                    _UDWORD TGI0V:8;                   /*   TGI0V      */
                    } BIT;                             /*              */
             } ICDIPR35;                               /*              */
       union {                                         /* ICDIPR36     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TGI0E:8;                   /*   TGI0E      */
                    _UDWORD TGI0F:8;                   /*   TGI0F      */
                    _UDWORD TGI1A:8;                   /*   TGI1A      */
                    _UDWORD TGI1B:8;                   /*   TGI1B      */
                    } BIT;                             /*              */
             } ICDIPR36;                               /*              */
       union {                                         /* ICDIPR37     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TGI1V:8;                   /*   TGI1V      */
                    _UDWORD TGI1U:8;                   /*   TGI1U      */
                    _UDWORD TGI2A:8;                   /*   TGI2A      */
                    _UDWORD TGI2B:8;                   /*   TGI2B      */
                    } BIT;                             /*              */
             } ICDIPR37;                               /*              */
       union {                                         /* ICDIPR38     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TGI2V:8;                   /*   TGI2V      */
                    _UDWORD TGI2U:8;                   /*   TGI2U      */
                    _UDWORD TGI3A:8;                   /*   TGI3A      */
                    _UDWORD TGI3B:8;                   /*   TGI3B      */
                    } BIT;                             /*              */
             } ICDIPR38;                               /*              */
       union {                                         /* ICDIPR39     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TGI3C:8;                   /*   TGI3C      */
                    _UDWORD TGI3D:8;                   /*   TGI3D      */
                    _UDWORD TGI3V:8;                   /*   TGI3V      */
                    _UDWORD TGI4A:8;                   /*   TGI4A      */
                    } BIT;                             /*              */
             } ICDIPR39;                               /*              */
       union {                                         /* ICDIPR40     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TGI4B:8;                   /*   TGI4B      */
                    _UDWORD TGI4C:8;                   /*   TGI4C      */
                    _UDWORD TGI4D:8;                   /*   TGI4D      */
                    _UDWORD TGI4V:8;                   /*   TGI4V      */
                    } BIT;                             /*              */
             } ICDIPR40;                               /*              */
       union {                                         /* ICDIPR41     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CMI1:8;                    /*   CMI1       */
                    _UDWORD CMI2:8;                    /*   CMI2       */
                    _UDWORD SGDEI0:8;                  /*   SGDEI0     */
                    _UDWORD SGDEI1:8;                  /*   SGDEI1     */
                    } BIT;                             /*              */
             } ICDIPR41;                               /*              */
       union {                                         /* ICDIPR42     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SGDEI2:8;                  /*   SGDEI2     */
                    _UDWORD SGDEI3:8;                  /*   SGDEI3     */
                    _UDWORD ADI:8;                     /*   ADI        */
                    _UDWORD ADWAR:8;                   /*   ADWAR      */
                    } BIT;                             /*              */
             } ICDIPR42;                               /*              */
       union {                                         /* ICDIPR43     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SSII0:8;                   /*   SSII0      */
                    _UDWORD SSIRXI0:8;                 /*   SSIRXI0    */
                    _UDWORD SSITXI0:8;                 /*   SSITXI0    */
                    _UDWORD SSII1:8;                   /*   SSII1      */
                    } BIT;                             /*              */
             } ICDIPR43;                               /*              */
       union {                                         /* ICDIPR44     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SSIRXI1:8;                 /*   SSIRXI1    */
                    _UDWORD SSITXI1:8;                 /*   SSITXI1    */
                    _UDWORD SSII2:8;                   /*   SSII2      */
                    _UDWORD SSIRTI2:8;                 /*   SSIRTI2    */
                    } BIT;                             /*              */
             } ICDIPR44;                               /*              */
       union {                                         /* ICDIPR45     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SSII3:8;                   /*   SSII3      */
                    _UDWORD SSIRXI3:8;                 /*   SSIRXI3    */
                    _UDWORD SSITXI3:8;                 /*   SSITXI3    */
                    _UDWORD SSII4:8;                   /*   SSII4      */
                    } BIT;                             /*              */
             } ICDIPR45;                               /*              */
       union {                                         /* ICDIPR46     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SSIRTI4:8;                 /*   SSIRTI4    */
                    _UDWORD SSII5:8;                   /*   SSII5      */
                    _UDWORD SSIRXI5:8;                 /*   SSIRXI5    */
                    _UDWORD SSITXI5:8;                 /*   SSITXI5    */
                    } BIT;                             /*              */
             } ICDIPR46;                               /*              */
       union {                                         /* ICDIPR47     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SPDIFI:8;                  /*   SPDIFI     */
                    _UDWORD TEI0:8;                    /*   TEI0       */
                    _UDWORD RI0:8;                     /*   RI0        */
                    _UDWORD TI0:8;                     /*   TI0        */
                    } BIT;                             /*              */
             } ICDIPR47;                               /*              */
       union {                                         /* ICDIPR48     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SPI0:8;                    /*   SPI0       */
                    _UDWORD STI0:8;                    /*   STI0       */
                    _UDWORD NAKI0:8;                   /*   NAKI0      */
                    _UDWORD ALI0:8;                    /*   ALI0       */
                    } BIT;                             /*              */
             } ICDIPR48;                               /*              */
       union {                                         /* ICDIPR49     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TMOI0:8;                   /*   TMOI0      */
                    _UDWORD TEI1:8;                    /*   TEI1       */
                    _UDWORD RI1:8;                     /*   RI1        */
                    _UDWORD TI1:8;                     /*   TI1        */
                    } BIT;                             /*              */
             } ICDIPR49;                               /*              */
       union {                                         /* ICDIPR50     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SPI1:8;                    /*   SPI1       */
                    _UDWORD STI1:8;                    /*   STI1       */
                    _UDWORD NAKI1:8;                   /*   NAKI1      */
                    _UDWORD ALI1:8;                    /*   ALI1       */
                    } BIT;                             /*              */
             } ICDIPR50;                               /*              */
       union {                                         /* ICDIPR51     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TMOI1:8;                   /*   TMOI1      */
                    _UDWORD TEI2:8;                    /*   TEI2       */
                    _UDWORD RI2:8;                     /*   RI2        */
                    _UDWORD TI2:8;                     /*   TI2        */
                    } BIT;                             /*              */
             } ICDIPR51;                               /*              */
       union {                                         /* ICDIPR52     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SPI2:8;                    /*   SPI2       */
                    _UDWORD STI2:8;                    /*   STI2       */
                    _UDWORD NAKI2:8;                   /*   NAKI2      */
                    _UDWORD ALI2:8;                    /*   ALI2       */
                    } BIT;                             /*              */
             } ICDIPR52;                               /*              */
       union {                                         /* ICDIPR53     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TMOI2:8;                   /*   TMOI2      */
                    _UDWORD TEI3:8;                    /*   TEI3       */
                    _UDWORD RI3:8;                     /*   RI3        */
                    _UDWORD TI3:8;                     /*   TI3        */
                    } BIT;                             /*              */
             } ICDIPR53;                               /*              */
       union {                                         /* ICDIPR54     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SPI3:8;                    /*   SPI3       */
                    _UDWORD STI3:8;                    /*   STI3       */
                    _UDWORD NAKI3:8;                   /*   NAKI3      */
                    _UDWORD ALI3:8;                    /*   ALI3       */
                    } BIT;                             /*              */
             } ICDIPR54;                               /*              */
       union {                                         /* ICDIPR55     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TMOI3:8;                   /*   TMOI3      */
                    _UDWORD BRI0:8;                    /*   BRI0       */
                    _UDWORD ERI0:8;                    /*   ERI0       */
                    _UDWORD RXI0:8;                    /*   RXI0       */
                    } BIT;                             /*              */
             } ICDIPR55;                               /*              */
       union {                                         /* ICDIPR56     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TXI0:8;                    /*   TXI0       */
                    _UDWORD BRI1:8;                    /*   BRI1       */
                    _UDWORD ERI1:8;                    /*   ERI1       */
                    _UDWORD RXI1:8;                    /*   RXI1       */
                    } BIT;                             /*              */
             } ICDIPR56;                               /*              */
       union {                                         /* ICDIPR57     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TXI1:8;                    /*   TXI1       */
                    _UDWORD BRI2:8;                    /*   BRI2       */
                    _UDWORD ERI2:8;                    /*   ERI2       */
                    _UDWORD RXI2:8;                    /*   RXI2       */
                    } BIT;                             /*              */
             } ICDIPR57;                               /*              */
       union {                                         /* ICDIPR58     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TXI2:8;                    /*   TXI2       */
                    _UDWORD BRI3:8;                    /*   BRI3       */
                    _UDWORD ERI3:8;                    /*   ERI3       */
                    _UDWORD RXI3:8;                    /*   RXI3       */
                    } BIT;                             /*              */
             } ICDIPR58;                               /*              */
       union {                                         /* ICDIPR59     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TXI3:8;                    /*   TXI3       */
                    _UDWORD BRI4:8;                    /*   BRI4       */
                    _UDWORD ERI4:8;                    /*   ERI4       */
                    _UDWORD RXI4:8;                    /*   RXI4       */
                    } BIT;                             /*              */
             } ICDIPR59;                               /*              */
       union {                                         /* ICDIPR60     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TXI4:8;                    /*   TXI4       */
                    _UDWORD BRI5:8;                    /*   BRI5       */
                    _UDWORD ERI5:8;                    /*   ERI5       */
                    _UDWORD RXI5:8;                    /*   RXI5       */
                    } BIT;                             /*              */
             } ICDIPR60;                               /*              */
       union {                                         /* ICDIPR61     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TXI5:8;                    /*   TXI5       */
                    _UDWORD BRI6:8;                    /*   BRI6       */
                    _UDWORD ERI6:8;                    /*   ERI6       */
                    _UDWORD RXI6:8;                    /*   RXI6       */
                    } BIT;                             /*              */
             } ICDIPR61;                               /*              */
       union {                                         /* ICDIPR62     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TXI6:8;                    /*   TXI6       */
                    _UDWORD BRI7:8;                    /*   BRI7       */
                    _UDWORD ERI7:8;                    /*   ERI7       */
                    _UDWORD RXI7:8;                    /*   RXI7       */
                    } BIT;                             /*              */
             } ICDIPR62;                               /*              */
       union {                                         /* ICDIPR63     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TXI7:8;                    /*   TXI7       */
                    _UDWORD GERI:8;                    /*   GERI       */
                    _UDWORD RFI:8;                     /*   RFI        */
                    _UDWORD CFRXI0:8;                  /*   CFRXI0     */
                    } BIT;                             /*              */
             } ICDIPR63;                               /*              */
       union {                                         /* ICDIPR64     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CERI0:8;                   /*   CERI0      */
                    _UDWORD CTXI0:8;                   /*   CTXI0      */
                    _UDWORD CFRXI1:8;                  /*   CFRXI1     */
                    _UDWORD CERI1:8;                   /*   CERI1      */
                    } BIT;                             /*              */
             } ICDIPR64;                               /*              */
       union {                                         /* ICDIPR65     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CTXI1:8;                   /*   CTXI1      */
                    _UDWORD CFRXI2:8;                  /*   CFRXI2     */
                    _UDWORD CERI2:8;                   /*   CERI2      */
                    _UDWORD CTXI2:8;                   /*   CTXI2      */
                    } BIT;                             /*              */
             } ICDIPR65;                               /*              */
       union {                                         /* ICDIPR66     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CFRXI3:8;                  /*   CFRXI3     */
                    _UDWORD CERI3:8;                   /*   CERI3      */
                    _UDWORD CTXI3:8;                   /*   CTXI3      */
                    _UDWORD CFRXI4:8;                  /*   CFRXI4     */
                    } BIT;                             /*              */
             } ICDIPR66;                               /*              */
       union {                                         /* ICDIPR67     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CERI4:8;                   /*   CERI4      */
                    _UDWORD CTXI4:8;                   /*   CTXI4      */
                    _UDWORD SPEI0:8;                   /*   SPEI0      */
                    _UDWORD SPRI0:8;                   /*   SPRI0      */
                    } BIT;                             /*              */
             } ICDIPR67;                               /*              */
       union {                                         /* ICDIPR68     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SPTI0:8;                   /*   SPTI0      */
                    _UDWORD SPEI1:8;                   /*   SPEI1      */
                    _UDWORD SPRI1:8;                   /*   SPRI1      */
                    _UDWORD SPTI1:8;                   /*   SPTI1      */
                    } BIT;                             /*              */
             } ICDIPR68;                               /*              */
       union {                                         /* ICDIPR69     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SPEI2:8;                   /*   SPEI2      */
                    _UDWORD SPRI2:8;                   /*   SPRI2      */
                    _UDWORD SPTI2:8;                   /*   SPTI2      */
                    _UDWORD SPEI3:8;                   /*   SPEI3      */
                    } BIT;                             /*              */
             } ICDIPR69;                               /*              */
       union {                                         /* ICDIPR70     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SPRI3:8;                   /*   SPRI3      */
                    _UDWORD SPTI3:8;                   /*   SPTI3      */
                    _UDWORD SPEI4:8;                   /*   SPEI4      */
                    _UDWORD SPRI4:8;                   /*   SPRI4      */
                    } BIT;                             /*              */
             } ICDIPR70;                               /*              */
       union {                                         /* ICDIPR71     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SPTI4:8;                   /*   SPTI4      */
                    _UDWORD IEBBTD:8;                  /*   IEBBTD     */
                    _UDWORD IEBBTERR:8;                /*   IEBBTERR   */
                    _UDWORD IEBBTSTA:8;                /*   IEBBTSTA   */
                    } BIT;                             /*              */
             } ICDIPR71;                               /*              */
       union {                                         /* ICDIPR72     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD IEBBTV:8;                  /*   IEBBTV     */
                    _UDWORD ISY:8;                     /*   ISY        */
                    _UDWORD IERR:8;                    /*   IERR       */
                    _UDWORD ITARG:8;                   /*   ITARG      */
                    } BIT;                             /*              */
             } ICDIPR72;                               /*              */
       union {                                         /* ICDIPR73     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD ISEC:8;                    /*   ISEC       */
                    _UDWORD IBUF:8;                    /*   IBUF       */
                    _UDWORD IREADY:8;                  /*   IREADY     */
                    _UDWORD FLSTE:8;                   /*   FLSTE      */
                    } BIT;                             /*              */
             } ICDIPR73;                               /*              */
       union {                                         /* ICDIPR74     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD FLTENDI:8;                 /*   FLTENDI    */
                    _UDWORD FLTREQ0I:8;                /*   FLTREQ0I   */
                    _UDWORD FLTREQ1I:8;                /*   FLTREQ1I   */
                    _UDWORD MMC0:8;                    /*   MMC0       */
                    } BIT;                             /*              */
             } ICDIPR74;                               /*              */
       union {                                         /* ICDIPR75     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD MMC1:8;                    /*   MMC1       */
                    _UDWORD MMC2:8;                    /*   MMC2       */
                    _UDWORD SDHI0_3:8;                 /*   SDHI0_3    */
                    _UDWORD SDHI0_0:8;                 /*   SDHI0_0    */
                    } BIT;                             /*              */
             } ICDIPR75;                               /*              */
       union {                                         /* ICDIPR76     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SDHI0_1:8;                 /*   SDHI0_1    */
                    _UDWORD SDHI1_3:8;                 /*   SDHI1_3    */
                    _UDWORD SDHI1_0:8;                 /*   SDHI1_0    */
                    _UDWORD SDHI1_1:8;                 /*   SDHI1_1    */
                    } BIT;                             /*              */
             } ICDIPR76;                               /*              */
       union {                                         /* ICDIPR77     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD ARM:8;                     /*   ARM        */
                    _UDWORD PRD:8;                     /*   PRD        */
                    _UDWORD CUP:8;                     /*   CUP        */
                    _UDWORD SCUAI0:8;                  /*   SCUAI0     */
                    } BIT;                             /*              */
             } ICDIPR77;                               /*              */
       union {                                         /* ICDIPR78     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SCUAI1:8;                  /*   SCUAI1     */
                    _UDWORD SCUFDI0:8;                 /*   SCUFDI0    */
                    _UDWORD SCUFDI1:8;                 /*   SCUFDI1    */
                    _UDWORD SCUFDI2:8;                 /*   SCUFDI2    */
                    } BIT;                             /*              */
             } ICDIPR78;                               /*              */
       union {                                         /* ICDIPR79     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SCUFDI3:8;                 /*   SCUFDI3    */
                    _UDWORD SCUFUI0:8;                 /*   SCUFUI0    */
                    _UDWORD SCUFUI1:8;                 /*   SCUFUI1    */
                    _UDWORD SCUFUI2:8;                 /*   SCUFUI2    */
                    } BIT;                             /*              */
             } ICDIPR79;                               /*              */
       union {                                         /* ICDIPR80     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SCUFUI3:8;                 /*   SCUFUI3    */
                    _UDWORD SCUDVI0:8;                 /*   SCUDVI0    */
                    _UDWORD SCUDVI1:8;                 /*   SCUDVI1    */
                    _UDWORD SCUDVI2:8;                 /*   SCUDVI2    */
                    } BIT;                             /*              */
             } ICDIPR80;                               /*              */
       union {                                         /* ICDIPR81     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SCUDVI3:8;                 /*   SCUDVI3    */
                    _UDWORD MLBCI:8;                   /*   MLBCI      */
                    _UDWORD MLBSI:8;                   /*   MLBSI      */
                    _UDWORD DRC0:8;                    /*   DRC0       */
                    } BIT;                             /*              */
             } ICDIPR81;                               /*              */
       union {                                         /* ICDIPR82     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD DRC1:8;                    /*   DRC1       */
                    _UDWORD :16;                       /*              */
                    _UDWORD LINI0_INT_T:8;             /*   LINI0_INT_T */
                    } BIT;                             /*              */
             } ICDIPR82;                               /*              */
       union {                                         /* ICDIPR83     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD LINI0_INT_R:8;             /*   LINI0_INT_R */
                    _UDWORD LINI0_INT_S:8;             /*   LINI0_INT_S */
                    _UDWORD LINI0_INT_M:8;             /*   LINI0_INT_M */
                    _UDWORD LINI1_INT_T:8;             /*   LINI1_INT_T */
                    } BIT;                             /*              */
             } ICDIPR83;                               /*              */
       union {                                         /* ICDIPR84     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD LINI1_INT_R:8;             /*   LINI1_INT_R */
                    _UDWORD LINI1_INT_S:8;             /*   LINI1_INT_S */
                    _UDWORD LINI1_INT_M:8;             /*   LINI1_INT_M */
                    _UDWORD :8;                        /*              */
                    } BIT;                             /*              */
             } ICDIPR84;                               /*              */
       _UBYTE wk9[4];                                  /*              */
       union {                                         /* ICDIPR86     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :24;                       /*              */
                    _UDWORD ERI0:8;                    /*   ERI0       */
                    } BIT;                             /*              */
             } ICDIPR86;                               /*              */
       union {                                         /* ICDIPR87     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD RXI0:8;                    /*   RXI0       */
                    _UDWORD TXI0:8;                    /*   TXI0       */
                    _UDWORD TEI0:8;                    /*   TEI0       */
                    _UDWORD ERI1:8;                    /*   ERI1       */
                    } BIT;                             /*              */
             } ICDIPR87;                               /*              */
       union {                                         /* ICDIPR88     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD RXI1:8;                    /*   RXI1       */
                    _UDWORD TXI1:8;                    /*   TXI1       */
                    _UDWORD TEI1:8;                    /*   TEI1       */
                    _UDWORD :8;                        /*              */
                    } BIT;                             /*              */
             } ICDIPR88;                               /*              */
       union {                                         /* ICDIPR89     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :24;                       /*              */
                    _UDWORD ETHERI:8;                  /*   ETHERI     */
                    } BIT;                             /*              */
             } ICDIPR89;                               /*              */
       _UBYTE wk10[4];                                 /*              */
       union {                                         /* ICDIPR91     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CEUI:8;                    /*   CEUI       */
                    _UDWORD INT_CSIH0TIR:8;            /*   INT_CSIH0TIR */
                    _UDWORD INT_CSIH0TIRE:8;           /*   INT_CSIH0TIRE */
                    _UDWORD INT_CSIH1TIC:8;            /*   INT_CSIH1TIC */
                    } BIT;                             /*              */
             } ICDIPR91;                               /*              */
       union {                                         /* ICDIPR92     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD INT_CSIH1TIJC:8;           /*   INT_CSIH1TIJC */
                    _UDWORD ECCE10:8;                  /*   ECCE10     */
                    _UDWORD ECCE20:8;                  /*   ECCE20     */
                    _UDWORD ECCOVF0:8;                 /*   ECCOVF0    */
                    } BIT;                             /*              */
             } ICDIPR92;                               /*              */
       union {                                         /* ICDIPR93     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD ECCE11:8;                  /*   ECCE11     */
                    _UDWORD ECCE21:8;                  /*   ECCE21     */
                    _UDWORD ECCOVF1:8;                 /*   ECCOVF1    */
                    _UDWORD ECCE12:8;                  /*   ECCE12     */
                    } BIT;                             /*              */
             } ICDIPR93;                               /*              */
       union {                                         /* ICDIPR94     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD ECCE22:8;                  /*   ECCE22     */
                    _UDWORD ECCOVF2:8;                 /*   ECCOVF2    */
                    _UDWORD ECCE13:8;                  /*   ECCE13     */
                    _UDWORD ECCE23:8;                  /*   ECCE23     */
                    } BIT;                             /*              */
             } ICDIPR94;                               /*              */
       union {                                         /* ICDIPR95     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD ECCOVF3:8;                 /*   ECCOVF3    */
                    _UDWORD H2XMLB_ERRINT:8;           /*   H2XMLB_ERRINT */
                    _UDWORD H2XIC1_ERRINT:8;           /*   H2XIC1_ERRINT */
                    _UDWORD X2HPERI1_ERRINT:8;         /*   X2HPERI1_ERRINT */
                    } BIT;                             /*              */
             } ICDIPR95;                               /*              */
       union {                                         /* ICDIPR96     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD X2HPERI2_ERRINT:8;         /*   X2HPERI2_ERRINT */
                    _UDWORD X2HPERI34_ERRINT:8;        /*   X2HPERI34_ERRINT */
                    _UDWORD X2HPERI5_ERRINT:8;         /*   X2HPERI5_ERRINT */
                    _UDWORD X2HPERI67_ERRINT:8;        /*   X2HPERI67_ERRINT */
                    } BIT;                             /*              */
             } ICDIPR96;                               /*              */
       union {                                         /* ICDIPR97     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD X2HDBGR_ERRINT:8;          /*   X2HDBGR_ERRINT */
                    _UDWORD PRRI:8;                    /*   PRRI       */
                    _UDWORD IFEI0:8;                   /*   IFEI0      */
                    _UDWORD OFFI0:8;                   /*   OFFI0      */
                    } BIT;                             /*              */
             } ICDIPR97;                               /*              */
       union {                                         /* ICDIPR98     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD PFVEI0:8;                  /*   PFVEI0     */
                    _UDWORD IFEI1:8;                   /*   IFEI1      */
                    _UDWORD OFFI1:8;                   /*   OFFI1      */
                    _UDWORD PFVEI1:8;                  /*   PFVEI1     */
                    } BIT;                             /*              */
             } ICDIPR98;                               /*              */
       _UBYTE wk11[20];                                /*              */
       union {                                         /* ICDIPR104    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT0:8;                   /*   TINT0      */
                    _UDWORD TINT1:8;                   /*   TINT1      */
                    _UDWORD TINT2:8;                   /*   TINT2      */
                    _UDWORD TINT3:8;                   /*   TINT3      */
                    } BIT;                             /*              */
             } ICDIPR104;                              /*              */
       union {                                         /* ICDIPR105    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT4:8;                   /*   TINT4      */
                    _UDWORD TINT5:8;                   /*   TINT5      */
                    _UDWORD TINT6:8;                   /*   TINT6      */
                    _UDWORD TINT7:8;                   /*   TINT7      */
                    } BIT;                             /*              */
             } ICDIPR105;                              /*              */
       union {                                         /* ICDIPR106    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT8:8;                   /*   TINT8      */
                    _UDWORD TINT9:8;                   /*   TINT9      */
                    _UDWORD TINT10:8;                  /*   TINT10     */
                    _UDWORD TINT11:8;                  /*   TINT11     */
                    } BIT;                             /*              */
             } ICDIPR106;                              /*              */
       union {                                         /* ICDIPR107    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT12:8;                  /*   TINT12     */
                    _UDWORD TINT13:8;                  /*   TINT13     */
                    _UDWORD TINT14:8;                  /*   TINT14     */
                    _UDWORD TINT15:8;                  /*   TINT15     */
                    } BIT;                             /*              */
             } ICDIPR107;                              /*              */
       union {                                         /* ICDIPR108    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT16:8;                  /*   TINT16     */
                    _UDWORD TINT17:8;                  /*   TINT17     */
                    _UDWORD TINT18:8;                  /*   TINT18     */
                    _UDWORD TINT19:8;                  /*   TINT19     */
                    } BIT;                             /*              */
             } ICDIPR108;                              /*              */
       union {                                         /* ICDIPR109    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT20:8;                  /*   TINT20     */
                    _UDWORD TINT21:8;                  /*   TINT21     */
                    _UDWORD TINT22:8;                  /*   TINT22     */
                    _UDWORD TINT23:8;                  /*   TINT23     */
                    } BIT;                             /*              */
             } ICDIPR109;                              /*              */
       union {                                         /* ICDIPR110    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT24:8;                  /*   TINT24     */
                    _UDWORD TINT25:8;                  /*   TINT25     */
                    _UDWORD TINT26:8;                  /*   TINT26     */
                    _UDWORD TINT27:8;                  /*   TINT27     */
                    } BIT;                             /*              */
             } ICDIPR110;                              /*              */
       union {                                         /* ICDIPR111    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT28:8;                  /*   TINT28     */
                    _UDWORD TINT29:8;                  /*   TINT29     */
                    _UDWORD TINT30:8;                  /*   TINT30     */
                    _UDWORD TINT31:8;                  /*   TINT31     */
                    } BIT;                             /*              */
             } ICDIPR111;                              /*              */
       union {                                         /* ICDIPR112    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT32:8;                  /*   TINT32     */
                    _UDWORD TINT33:8;                  /*   TINT33     */
                    _UDWORD TINT34:8;                  /*   TINT34     */
                    _UDWORD TINT35:8;                  /*   TINT35     */
                    } BIT;                             /*              */
             } ICDIPR112;                              /*              */
       union {                                         /* ICDIPR113    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT36:8;                  /*   TINT36     */
                    _UDWORD TINT37:8;                  /*   TINT37     */
                    _UDWORD TINT38:8;                  /*   TINT38     */
                    _UDWORD TINT39:8;                  /*   TINT39     */
                    } BIT;                             /*              */
             } ICDIPR113;                              /*              */
       union {                                         /* ICDIPR114    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT40:8;                  /*   TINT40     */
                    _UDWORD TINT41:8;                  /*   TINT41     */
                    _UDWORD TINT42:8;                  /*   TINT42     */
                    _UDWORD TINT43:8;                  /*   TINT43     */
                    } BIT;                             /*              */
             } ICDIPR114;                              /*              */
       union {                                         /* ICDIPR115    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT44:8;                  /*   TINT44     */
                    _UDWORD TINT45:8;                  /*   TINT45     */
                    _UDWORD TINT46:8;                  /*   TINT46     */
                    _UDWORD TINT47:8;                  /*   TINT47     */
                    } BIT;                             /*              */
             } ICDIPR115;                              /*              */
       union {                                         /* ICDIPR116    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT48:8;                  /*   TINT48     */
                    _UDWORD TINT49:8;                  /*   TINT49     */
                    _UDWORD TINT50:8;                  /*   TINT50     */
                    _UDWORD TINT51:8;                  /*   TINT51     */
                    } BIT;                             /*              */
             } ICDIPR116;                              /*              */
       union {                                         /* ICDIPR117    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT52:8;                  /*   TINT52     */
                    _UDWORD TINT53:8;                  /*   TINT53     */
                    _UDWORD TINT54:8;                  /*   TINT54     */
                    _UDWORD TINT55:8;                  /*   TINT55     */
                    } BIT;                             /*              */
             } ICDIPR117;                              /*              */
       union {                                         /* ICDIPR118    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT56:8;                  /*   TINT56     */
                    _UDWORD TINT57:8;                  /*   TINT57     */
                    _UDWORD TINT58:8;                  /*   TINT58     */
                    _UDWORD TINT59:8;                  /*   TINT59     */
                    } BIT;                             /*              */
             } ICDIPR118;                              /*              */
       union {                                         /* ICDIPR119    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT60:8;                  /*   TINT60     */
                    _UDWORD TINT61:8;                  /*   TINT61     */
                    _UDWORD TINT62:8;                  /*   TINT62     */
                    _UDWORD TINT63:8;                  /*   TINT63     */
                    } BIT;                             /*              */
             } ICDIPR119;                              /*              */
       union {                                         /* ICDIPR120    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT64:8;                  /*   TINT64     */
                    _UDWORD TINT65:8;                  /*   TINT65     */
                    _UDWORD TINT66:8;                  /*   TINT66     */
                    _UDWORD TINT67:8;                  /*   TINT67     */
                    } BIT;                             /*              */
             } ICDIPR120;                              /*              */
       union {                                         /* ICDIPR121    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT68:8;                  /*   TINT68     */
                    _UDWORD TINT69:8;                  /*   TINT69     */
                    _UDWORD TINT70:8;                  /*   TINT70     */
                    _UDWORD TINT71:8;                  /*   TINT71     */
                    } BIT;                             /*              */
             } ICDIPR121;                              /*              */
       union {                                         /* ICDIPR122    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT72:8;                  /*   TINT72     */
                    _UDWORD TINT73:8;                  /*   TINT73     */
                    _UDWORD TINT74:8;                  /*   TINT74     */
                    _UDWORD TINT75:8;                  /*   TINT75     */
                    } BIT;                             /*              */
             } ICDIPR122;                              /*              */
       union {                                         /* ICDIPR123    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT76:8;                  /*   TINT76     */
                    _UDWORD TINT77:8;                  /*   TINT77     */
                    _UDWORD TINT78:8;                  /*   TINT78     */
                    _UDWORD TINT79:8;                  /*   TINT79     */
                    } BIT;                             /*              */
             } ICDIPR123;                              /*              */
       union {                                         /* ICDIPR124    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT80:8;                  /*   TINT80     */
                    _UDWORD TINT81:8;                  /*   TINT81     */
                    _UDWORD TINT82:8;                  /*   TINT82     */
                    _UDWORD TINT83:8;                  /*   TINT83     */
                    } BIT;                             /*              */
             } ICDIPR124;                              /*              */
       union {                                         /* ICDIPR125    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT84:8;                  /*   TINT84     */
                    _UDWORD TINT85:8;                  /*   TINT85     */
                    _UDWORD TINT86:8;                  /*   TINT86     */
                    _UDWORD TINT87:8;                  /*   TINT87     */
                    } BIT;                             /*              */
             } ICDIPR125;                              /*              */
       union {                                         /* ICDIPR126    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT88:8;                  /*   TINT88     */
                    _UDWORD TINT89:8;                  /*   TINT89     */
                    _UDWORD TINT90:8;                  /*   TINT90     */
                    _UDWORD TINT91:8;                  /*   TINT91     */
                    } BIT;                             /*              */
             } ICDIPR126;                              /*              */
       union {                                         /* ICDIPR127    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT92:8;                  /*   TINT92     */
                    _UDWORD TINT93:8;                  /*   TINT93     */
                    _UDWORD TINT94:8;                  /*   TINT94     */
                    _UDWORD TINT95:8;                  /*   TINT95     */
                    } BIT;                             /*              */
             } ICDIPR127;                              /*              */
       union {                                         /* ICDIPR128    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT96:8;                  /*   TINT96     */
                    _UDWORD TINT97:8;                  /*   TINT97     */
                    _UDWORD TINT98:8;                  /*   TINT98     */
                    _UDWORD TINT99:8;                  /*   TINT99     */
                    } BIT;                             /*              */
             } ICDIPR128;                              /*              */
       union {                                         /* ICDIPR129    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT100:8;                 /*   TINT100    */
                    _UDWORD TINT101:8;                 /*   TINT101    */
                    _UDWORD TINT102:8;                 /*   TINT102    */
                    _UDWORD TINT103:8;                 /*   TINT103    */
                    } BIT;                             /*              */
             } ICDIPR129;                              /*              */
       union {                                         /* ICDIPR130    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT104:8;                 /*   TINT104    */
                    _UDWORD TINT105:8;                 /*   TINT105    */
                    _UDWORD TINT106:8;                 /*   TINT106    */
                    _UDWORD TINT107:8;                 /*   TINT107    */
                    } BIT;                             /*              */
             } ICDIPR130;                              /*              */
       union {                                         /* ICDIPR131    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT108:8;                 /*   TINT108    */
                    _UDWORD TINT109:8;                 /*   TINT109    */
                    _UDWORD TINT110:8;                 /*   TINT110    */
                    _UDWORD TINT111:8;                 /*   TINT111    */
                    } BIT;                             /*              */
             } ICDIPR131;                              /*              */
       union {                                         /* ICDIPR132    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT112:8;                 /*   TINT112    */
                    _UDWORD TINT113:8;                 /*   TINT113    */
                    _UDWORD TINT114:8;                 /*   TINT114    */
                    _UDWORD TINT115:8;                 /*   TINT115    */
                    } BIT;                             /*              */
             } ICDIPR132;                              /*              */
       union {                                         /* ICDIPR133    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT116:8;                 /*   TINT116    */
                    _UDWORD TINT117:8;                 /*   TINT117    */
                    _UDWORD TINT118:8;                 /*   TINT118    */
                    _UDWORD TINT119:8;                 /*   TINT119    */
                    } BIT;                             /*              */
             } ICDIPR133;                              /*              */
       union {                                         /* ICDIPR134    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT120:8;                 /*   TINT120    */
                    _UDWORD TINT121:8;                 /*   TINT121    */
                    _UDWORD TINT122:8;                 /*   TINT122    */
                    _UDWORD TINT123:8;                 /*   TINT123    */
                    } BIT;                             /*              */
             } ICDIPR134;                              /*              */
       union {                                         /* ICDIPR135    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT124:8;                 /*   TINT124    */
                    _UDWORD TINT125:8;                 /*   TINT125    */
                    _UDWORD TINT126:8;                 /*   TINT126    */
                    _UDWORD TINT127:8;                 /*   TINT127    */
                    } BIT;                             /*              */
             } ICDIPR135;                              /*              */
       union {                                         /* ICDIPR136    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT128:8;                 /*   TINT128    */
                    _UDWORD TINT129:8;                 /*   TINT129    */
                    _UDWORD TINT130:8;                 /*   TINT130    */
                    _UDWORD TINT131:8;                 /*   TINT131    */
                    } BIT;                             /*              */
             } ICDIPR136;                              /*              */
       union {                                         /* ICDIPR137    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT132:8;                 /*   TINT132    */
                    _UDWORD TINT133:8;                 /*   TINT133    */
                    _UDWORD TINT134:8;                 /*   TINT134    */
                    _UDWORD TINT135:8;                 /*   TINT135    */
                    } BIT;                             /*              */
             } ICDIPR137;                              /*              */
       union {                                         /* ICDIPR138    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT136:8;                 /*   TINT136    */
                    _UDWORD TINT137:8;                 /*   TINT137    */
                    _UDWORD TINT138:8;                 /*   TINT138    */
                    _UDWORD TINT139:8;                 /*   TINT139    */
                    } BIT;                             /*              */
             } ICDIPR138;                              /*              */
       union {                                         /* ICDIPR139    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT140:8;                 /*   TINT140    */
                    _UDWORD TINT141:8;                 /*   TINT141    */
                    _UDWORD TINT142:8;                 /*   TINT142    */
                    _UDWORD TINT143:8;                 /*   TINT143    */
                    } BIT;                             /*              */
             } ICDIPR139;                              /*              */
       union {                                         /* ICDIPR140    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT144:8;                 /*   TINT144    */
                    _UDWORD TINT145:8;                 /*   TINT145    */
                    _UDWORD TINT146:8;                 /*   TINT146    */
                    _UDWORD TINT147:8;                 /*   TINT147    */
                    } BIT;                             /*              */
             } ICDIPR140;                              /*              */
       union {                                         /* ICDIPR141    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT148:8;                 /*   TINT148    */
                    _UDWORD TINT149:8;                 /*   TINT149    */
                    _UDWORD TINT150:8;                 /*   TINT150    */
                    _UDWORD TINT151:8;                 /*   TINT151    */
                    } BIT;                             /*              */
             } ICDIPR141;                              /*              */
       union {                                         /* ICDIPR142    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT152:8;                 /*   TINT152    */
                    _UDWORD TINT153:8;                 /*   TINT153    */
                    _UDWORD TINT154:8;                 /*   TINT154    */
                    _UDWORD TINT155:8;                 /*   TINT155    */
                    } BIT;                             /*              */
             } ICDIPR142;                              /*              */
       union {                                         /* ICDIPR143    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT156:8;                 /*   TINT156    */
                    _UDWORD TINT157:8;                 /*   TINT157    */
                    _UDWORD TINT158:8;                 /*   TINT158    */
                    _UDWORD TINT159:8;                 /*   TINT159    */
                    } BIT;                             /*              */
             } ICDIPR143;                              /*              */
       union {                                         /* ICDIPR144    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT160:8;                 /*   TINT160    */
                    _UDWORD TINT161:8;                 /*   TINT161    */
                    _UDWORD TINT162:8;                 /*   TINT162    */
                    _UDWORD :8;                        /*              */
                    } BIT;                             /*              */
             } ICDIPR144;                              /*              */
       _UBYTE wk12[444];                               /*              */
       union {                                         /* ICDIPTR0     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SW0:8;                     /*   SW0        */
                    _UDWORD SW1:8;                     /*   SW1        */
                    _UDWORD SW2:8;                     /*   SW2        */
                    _UDWORD SW3:8;                     /*   SW3        */
                    } BIT;                             /*              */
             } ICDIPTR0;                               /*              */
       union {                                         /* ICDIPTR1     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SW4:8;                     /*   SW4        */
                    _UDWORD SW5:8;                     /*   SW5        */
                    _UDWORD SW6:8;                     /*   SW6        */
                    _UDWORD SW7:8;                     /*   SW7        */
                    } BIT;                             /*              */
             } ICDIPTR1;                               /*              */
       union {                                         /* ICDIPTR2     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SW8:8;                     /*   SW8        */
                    _UDWORD SW9:8;                     /*   SW9        */
                    _UDWORD SW10:8;                    /*   SW10       */
                    _UDWORD SW11:8;                    /*   SW11       */
                    } BIT;                             /*              */
             } ICDIPTR2;                               /*              */
       union {                                         /* ICDIPTR3     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SW12:8;                    /*   SW12       */
                    _UDWORD SW13:8;                    /*   SW13       */
                    _UDWORD SW14:8;                    /*   SW14       */
                    _UDWORD SW15:8;                    /*   SW15       */
                    } BIT;                             /*              */
             } ICDIPTR3;                               /*              */
       union {                                         /* ICDIPTR4     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD PMUIRQ0:8;                 /*   PMUIRQ0    */
                    _UDWORD COMMRX0:8;                 /*   COMMRX0    */
                    _UDWORD COMMTX0:8;                 /*   COMMTX0    */
                    _UDWORD CTIIRQ0:8;                 /*   CTIIRQ0    */
                    } BIT;                             /*              */
             } ICDIPTR4;                               /*              */
       _UBYTE wk13[12];                                /*              */
       union {                                         /* ICDIPTR8     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD IRQ0:8;                    /*   IRQ0       */
                    _UDWORD IRQ1:8;                    /*   IRQ1       */
                    _UDWORD IRQ2:8;                    /*   IRQ2       */
                    _UDWORD IRQ3:8;                    /*   IRQ3       */
                    } BIT;                             /*              */
             } ICDIPTR8;                               /*              */
       union {                                         /* ICDIPTR9     */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD IRQ4:8;                    /*   IRQ4       */
                    _UDWORD IRQ5:8;                    /*   IRQ5       */
                    _UDWORD IRQ6:8;                    /*   IRQ6       */
                    _UDWORD IRQ7:8;                    /*   IRQ7       */
                    } BIT;                             /*              */
             } ICDIPTR9;                               /*              */
       union {                                         /* ICDIPTR10    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD PL310ERR:8;                /*   PL310ERR   */
                    _UDWORD DMAINT0:8;                 /*   DMAINT0    */
                    _UDWORD DMAINT1:8;                 /*   DMAINT1    */
                    _UDWORD DMAINT2:8;                 /*   DMAINT2    */
                    } BIT;                             /*              */
             } ICDIPTR10;                              /*              */
       union {                                         /* ICDIPTR11    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD DMAINT3:8;                 /*   DMAINT3    */
                    _UDWORD DMAINT4:8;                 /*   DMAINT4    */
                    _UDWORD DMAINT5:8;                 /*   DMAINT5    */
                    _UDWORD DMAINT6:8;                 /*   DMAINT6    */
                    } BIT;                             /*              */
             } ICDIPTR11;                              /*              */
       union {                                         /* ICDIPTR12    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD DMAINT7:8;                 /*   DMAINT7    */
                    _UDWORD DMAINT8:8;                 /*   DMAINT8    */
                    _UDWORD DMAINT9:8;                 /*   DMAINT9    */
                    _UDWORD DMAINT10:8;                /*   DMAINT10   */
                    } BIT;                             /*              */
             } ICDIPTR12;                              /*              */
       union {                                         /* ICDIPTR13    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD DMAINT11:8;                /*   DMAINT11   */
                    _UDWORD DMAINT12:8;                /*   DMAINT12   */
                    _UDWORD DMAINT13:8;                /*   DMAINT13   */
                    _UDWORD DMAINT14:8;                /*   DMAINT14   */
                    } BIT;                             /*              */
             } ICDIPTR13;                              /*              */
       union {                                         /* ICDIPTR14    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD DMAINT15:8;                /*   DMAINT15   */
                    _UDWORD DMAERR:8;                  /*   DMAERR     */
                    _UDWORD :16;                       /*              */
                    } BIT;                             /*              */
             } ICDIPTR14;                              /*              */
       _UBYTE wk14[12];                                /*              */
       union {                                         /* ICDIPTR18    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :8;                        /*              */
                    _UDWORD USBI0:8;                   /*   USBI0      */
                    _UDWORD USBI1:8;                   /*   USBI1      */
                    _UDWORD S0_VI_VSYNC0:8;            /*   S0_VI_VSYNC0 */
                    } BIT;                             /*              */
             } ICDIPTR18;                              /*              */
       union {                                         /* ICDIPTR19    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD S0_LO_VSYNC0:8;            /*   S0_LO_VSYNC0 */
                    _UDWORD S0_VSYNCERR0:8;            /*   S0_VSYNCERR0 */
                    _UDWORD GR3_VLINE0:8;              /*   GR3_VLINE0 */
                    _UDWORD S0_VFIELD0:8;              /*   S0_VFIELD0 */
                    } BIT;                             /*              */
             } ICDIPTR19;                              /*              */
       union {                                         /* ICDIPTR20    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD IV1_VBUFERR0:8;            /*   IV1_VBUFERR0 */
                    _UDWORD IV3_VBUFERR0:8;            /*   IV3_VBUFERR0 */
                    _UDWORD IV5_VBUFERR0:8;            /*   IV5_VBUFERR0 */
                    _UDWORD IV6_VBUFERR0:8;            /*   IV6_VBUFERR0 */
                    } BIT;                             /*              */
             } ICDIPTR20;                              /*              */
       union {                                         /* ICDIPTR21    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD S0_WLINE0:8;               /*   S0_WLINE0  */
                    _UDWORD S1_VI_VSYNC0:8;            /*   S1_VI_VSYNC0 */
                    _UDWORD S1_LO_VSYNC0:8;            /*   S1_LO_VSYNC0 */
                    _UDWORD S1_VSYNCERR0:8;            /*   S1_VSYNCERR0 */
                    } BIT;                             /*              */
             } ICDIPTR21;                              /*              */
       union {                                         /* ICDIPTR22    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD S1_VFIELD0:8;              /*   S1_VFIELD0 */
                    _UDWORD IV2_VBUFERR0:8;            /*   IV2_VBUFERR0 */
                    _UDWORD IV4_VBUFERR0:8;            /*   IV4_VBUFERR0 */
                    _UDWORD S1_WLINE0:8;               /*   S1_WLINE0  */
                    } BIT;                             /*              */
             } ICDIPTR22;                              /*              */
       union {                                         /* ICDIPTR23    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD OIR_VI_VSYNC0:8;           /*   OIR_VI_VSYNC0 */
                    _UDWORD OIR_LO_VSYNC0:8;           /*   OIR_LO_VSYNC0 */
                    _UDWORD OIR_VSYNCERR0:8;           /*   OIR_VSYNCERR0 */
                    _UDWORD OIR_VFIELD0:8;             /*   OIR_VFIELD0 */
                    } BIT;                             /*              */
             } ICDIPTR23;                              /*              */
       union {                                         /* ICDIPTR24    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD IV7_VBUFERR0:8;            /*   IV7_VBUFERR0 */
                    _UDWORD IV8_VBUFERR0:8;            /*   IV8_VBUFERR0 */
                    _UDWORD OIR_WLINE0:8;              /*   OIR_WLINE0 */
                    _UDWORD S0_VI_VSYNC1:8;            /*   S0_VI_VSYNC1 */
                    } BIT;                             /*              */
             } ICDIPTR24;                              /*              */
       union {                                         /* ICDIPTR25    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD S0_LO_VSYNC1:8;            /*   S0_LO_VSYNC1 */
                    _UDWORD S0_VSYNCERR1:8;            /*   S0_VSYNCERR1 */
                    _UDWORD GR3_VLINE1:8;              /*   GR3_VLINE1 */
                    _UDWORD S0_VFIELD1:8;              /*   S0_VFIELD1 */
                    } BIT;                             /*              */
             } ICDIPTR25;                              /*              */
       union {                                         /* ICDIPTR26    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD IV1_VBUFERR1:8;            /*   IV1_VBUFERR1 */
                    _UDWORD IV3_VBUFERR1:8;            /*   IV3_VBUFERR1 */
                    _UDWORD IV5_VBUFERR1:8;            /*   IV5_VBUFERR1 */
                    _UDWORD IV6_VBUFERR1:8;            /*   IV6_VBUFERR1 */
                    } BIT;                             /*              */
             } ICDIPTR26;                              /*              */
       union {                                         /* ICDIPTR27    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD S0_WLINE1:8;               /*   S0_WLINE1  */
                    _UDWORD S1_VI_VSYNC1:8;            /*   S1_VI_VSYNC1 */
                    _UDWORD S1_LO_VSYNC1:8;            /*   S1_LO_VSYNC1 */
                    _UDWORD S1_VSYNCERR1:8;            /*   S1_VSYNCERR1 */
                    } BIT;                             /*              */
             } ICDIPTR27;                              /*              */
       union {                                         /* ICDIPTR28    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD S1_VFIELD1:8;              /*   S1_VFIELD1 */
                    _UDWORD IV2_VBUFERR1:8;            /*   IV2_VBUFERR1 */
                    _UDWORD IV4_VBUFERR1:8;            /*   IV4_VBUFERR1 */
                    _UDWORD S1_WLINE1:8;               /*   S1_WLINE1  */
                    } BIT;                             /*              */
             } ICDIPTR28;                              /*              */
       union {                                         /* ICDIPTR29    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD OIR_VI_VSYNC1:8;           /*   OIR_VI_VSYNC1 */
                    _UDWORD OIR_LO_VSYNC1:8;           /*   OIR_LO_VSYNC1 */
                    _UDWORD OIR_VLINE1:8;              /*   OIR_VLINE1 */
                    _UDWORD OIR_VFIELD1:8;             /*   OIR_VFIELD1 */
                    } BIT;                             /*              */
             } ICDIPTR29;                              /*              */
       union {                                         /* ICDIPTR30    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD IV7_VBUFERR1:8;            /*   IV7_VBUFERR1 */
                    _UDWORD IV8_VBUFERR1:8;            /*   IV8_VBUFERR1 */
                    _UDWORD OIR_WLINE1:8;              /*   OIR_WLINE1 */
                    _UDWORD IMRDI:8;                   /*   IMRDI      */
                    } BIT;                             /*              */
             } ICDIPTR30;                              /*              */
       union {                                         /* ICDIPTR31    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD IMR2I0:8;                  /*   IMR2I0     */
                    _UDWORD IMR2I1:8;                  /*   IMR2I1     */
                    _UDWORD JEDI:8;                    /*   JEDI       */
                    _UDWORD JDTI:8;                    /*   JDTI       */
                    } BIT;                             /*              */
             } ICDIPTR31;                              /*              */
       union {                                         /* ICDIPTR32    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CMP0:8;                    /*   CMP0       */
                    _UDWORD CMP1:8;                    /*   CMP1       */
                    _UDWORD INT0:8;                    /*   INT0       */
                    _UDWORD INT1:8;                    /*   INT1       */
                    } BIT;                             /*              */
             } ICDIPTR32;                              /*              */
       union {                                         /* ICDIPTR33    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD INT2:8;                    /*   INT2       */
                    _UDWORD INT3:8;                    /*   INT3       */
                    _UDWORD OSTMI0:8;                  /*   OSTMI0     */
                    _UDWORD OSTMI1:8;                  /*   OSTMI1     */
                    } BIT;                             /*              */
             } ICDIPTR33;                              /*              */
       union {                                         /* ICDIPTR34    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CMI:8;                     /*   CMI        */
                    _UDWORD WTOUT:8;                   /*   WTOUT      */
                    _UDWORD ITI:8;                     /*   ITI        */
                    _UDWORD TGI0A:8;                   /*   TGI0A      */
                    } BIT;                             /*              */
             } ICDIPTR34;                              /*              */
       union {                                         /* ICDIPTR35    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TGI0B:8;                   /*   TGI0B      */
                    _UDWORD TGI0C:8;                   /*   TGI0C      */
                    _UDWORD TGI0D:8;                   /*   TGI0D      */
                    _UDWORD TGI0V:8;                   /*   TGI0V      */
                    } BIT;                             /*              */
             } ICDIPTR35;                              /*              */
       union {                                         /* ICDIPTR36    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TGI0E:8;                   /*   TGI0E      */
                    _UDWORD TGI0F:8;                   /*   TGI0F      */
                    _UDWORD TGI1A:8;                   /*   TGI1A      */
                    _UDWORD TGI1B:8;                   /*   TGI1B      */
                    } BIT;                             /*              */
             } ICDIPTR36;                              /*              */
       union {                                         /* ICDIPTR37    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TGI1V:8;                   /*   TGI1V      */
                    _UDWORD TGI1U:8;                   /*   TGI1U      */
                    _UDWORD TGI2A:8;                   /*   TGI2A      */
                    _UDWORD TGI2B:8;                   /*   TGI2B      */
                    } BIT;                             /*              */
             } ICDIPTR37;                              /*              */
       union {                                         /* ICDIPTR38    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TGI2V:8;                   /*   TGI2V      */
                    _UDWORD TGI2U:8;                   /*   TGI2U      */
                    _UDWORD TGI3A:8;                   /*   TGI3A      */
                    _UDWORD TGI3B:8;                   /*   TGI3B      */
                    } BIT;                             /*              */
             } ICDIPTR38;                              /*              */
       union {                                         /* ICDIPTR39    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TGI3C:8;                   /*   TGI3C      */
                    _UDWORD TGI3D:8;                   /*   TGI3D      */
                    _UDWORD TGI3V:8;                   /*   TGI3V      */
                    _UDWORD TGI4A:8;                   /*   TGI4A      */
                    } BIT;                             /*              */
             } ICDIPTR39;                              /*              */
       union {                                         /* ICDIPTR40    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TGI4B:8;                   /*   TGI4B      */
                    _UDWORD TGI4C:8;                   /*   TGI4C      */
                    _UDWORD TGI4D:8;                   /*   TGI4D      */
                    _UDWORD TGI4V:8;                   /*   TGI4V      */
                    } BIT;                             /*              */
             } ICDIPTR40;                              /*              */
       union {                                         /* ICDIPTR41    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CMI1:8;                    /*   CMI1       */
                    _UDWORD CMI2:8;                    /*   CMI2       */
                    _UDWORD SGDEI0:8;                  /*   SGDEI0     */
                    _UDWORD SGDEI1:8;                  /*   SGDEI1     */
                    } BIT;                             /*              */
             } ICDIPTR41;                              /*              */
       union {                                         /* ICDIPTR42    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SGDEI2:8;                  /*   SGDEI2     */
                    _UDWORD SGDEI3:8;                  /*   SGDEI3     */
                    _UDWORD ADI:8;                     /*   ADI        */
                    _UDWORD ADWAR:8;                   /*   ADWAR      */
                    } BIT;                             /*              */
             } ICDIPTR42;                              /*              */
       union {                                         /* ICDIPTR43    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SSII0:8;                   /*   SSII0      */
                    _UDWORD SSIRXI0:8;                 /*   SSIRXI0    */
                    _UDWORD SSITXI0:8;                 /*   SSITXI0    */
                    _UDWORD SSII1:8;                   /*   SSII1      */
                    } BIT;                             /*              */
             } ICDIPTR43;                              /*              */
       union {                                         /* ICDIPTR44    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SSIRXI1:8;                 /*   SSIRXI1    */
                    _UDWORD SSITXI1:8;                 /*   SSITXI1    */
                    _UDWORD SSII2:8;                   /*   SSII2      */
                    _UDWORD SSIRTI2:8;                 /*   SSIRTI2    */
                    } BIT;                             /*              */
             } ICDIPTR44;                              /*              */
       union {                                         /* ICDIPTR45    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SSII3:8;                   /*   SSII3      */
                    _UDWORD SSIRXI3:8;                 /*   SSIRXI3    */
                    _UDWORD SSITXI3:8;                 /*   SSITXI3    */
                    _UDWORD SSII4:8;                   /*   SSII4      */
                    } BIT;                             /*              */
             } ICDIPTR45;                              /*              */
       union {                                         /* ICDIPTR46    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SSIRTI4:8;                 /*   SSIRTI4    */
                    _UDWORD SSII5:8;                   /*   SSII5      */
                    _UDWORD SSIRXI5:8;                 /*   SSIRXI5    */
                    _UDWORD SSITXI5:8;                 /*   SSITXI5    */
                    } BIT;                             /*              */
             } ICDIPTR46;                              /*              */
       union {                                         /* ICDIPTR47    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SPDIFI:8;                  /*   SPDIFI     */
                    _UDWORD TEI0:8;                    /*   TEI0       */
                    _UDWORD RI0:8;                     /*   RI0        */
                    _UDWORD TI0:8;                     /*   TI0        */
                    } BIT;                             /*              */
             } ICDIPTR47;                              /*              */
       union {                                         /* ICDIPTR48    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SPI0:8;                    /*   SPI0       */
                    _UDWORD STI0:8;                    /*   STI0       */
                    _UDWORD NAKI0:8;                   /*   NAKI0      */
                    _UDWORD ALI0:8;                    /*   ALI0       */
                    } BIT;                             /*              */
             } ICDIPTR48;                              /*              */
       union {                                         /* ICDIPTR49    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TMOI0:8;                   /*   TMOI0      */
                    _UDWORD TEI1:8;                    /*   TEI1       */
                    _UDWORD RI1:8;                     /*   RI1        */
                    _UDWORD TI1:8;                     /*   TI1        */
                    } BIT;                             /*              */
             } ICDIPTR49;                              /*              */
       union {                                         /* ICDIPTR50    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SPI1:8;                    /*   SPI1       */
                    _UDWORD STI1:8;                    /*   STI1       */
                    _UDWORD NAKI1:8;                   /*   NAKI1      */
                    _UDWORD ALI1:8;                    /*   ALI1       */
                    } BIT;                             /*              */
             } ICDIPTR50;                              /*              */
       union {                                         /* ICDIPTR51    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TMOI1:8;                   /*   TMOI1      */
                    _UDWORD TEI2:8;                    /*   TEI2       */
                    _UDWORD RI2:8;                     /*   RI2        */
                    _UDWORD TI2:8;                     /*   TI2        */
                    } BIT;                             /*              */
             } ICDIPTR51;                              /*              */
       union {                                         /* ICDIPTR52    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SPI2:8;                    /*   SPI2       */
                    _UDWORD STI2:8;                    /*   STI2       */
                    _UDWORD NAKI2:8;                   /*   NAKI2      */
                    _UDWORD ALI2:8;                    /*   ALI2       */
                    } BIT;                             /*              */
             } ICDIPTR52;                              /*              */
       union {                                         /* ICDIPTR53    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TMOI2:8;                   /*   TMOI2      */
                    _UDWORD TEI3:8;                    /*   TEI3       */
                    _UDWORD RI3:8;                     /*   RI3        */
                    _UDWORD TI3:8;                     /*   TI3        */
                    } BIT;                             /*              */
             } ICDIPTR53;                              /*              */
       union {                                         /* ICDIPTR54    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SPI3:8;                    /*   SPI3       */
                    _UDWORD STI3:8;                    /*   STI3       */
                    _UDWORD NAKI3:8;                   /*   NAKI3      */
                    _UDWORD ALI3:8;                    /*   ALI3       */
                    } BIT;                             /*              */
             } ICDIPTR54;                              /*              */
       union {                                         /* ICDIPTR55    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TMOI3:8;                   /*   TMOI3      */
                    _UDWORD BRI0:8;                    /*   BRI0       */
                    _UDWORD ERI0:8;                    /*   ERI0       */
                    _UDWORD RXI0:8;                    /*   RXI0       */
                    } BIT;                             /*              */
             } ICDIPTR55;                              /*              */
       union {                                         /* ICDIPTR56    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TXI0:8;                    /*   TXI0       */
                    _UDWORD BRI1:8;                    /*   BRI1       */
                    _UDWORD ERI1:8;                    /*   ERI1       */
                    _UDWORD RXI1:8;                    /*   RXI1       */
                    } BIT;                             /*              */
             } ICDIPTR56;                              /*              */
       union {                                         /* ICDIPTR57    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TXI1:8;                    /*   TXI1       */
                    _UDWORD BRI2:8;                    /*   BRI2       */
                    _UDWORD ERI2:8;                    /*   ERI2       */
                    _UDWORD RXI2:8;                    /*   RXI2       */
                    } BIT;                             /*              */
             } ICDIPTR57;                              /*              */
       union {                                         /* ICDIPTR58    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TXI2:8;                    /*   TXI2       */
                    _UDWORD BRI3:8;                    /*   BRI3       */
                    _UDWORD ERI3:8;                    /*   ERI3       */
                    _UDWORD RXI3:8;                    /*   RXI3       */
                    } BIT;                             /*              */
             } ICDIPTR58;                              /*              */
       union {                                         /* ICDIPTR59    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TXI3:8;                    /*   TXI3       */
                    _UDWORD BRI4:8;                    /*   BRI4       */
                    _UDWORD ERI4:8;                    /*   ERI4       */
                    _UDWORD RXI4:8;                    /*   RXI4       */
                    } BIT;                             /*              */
             } ICDIPTR59;                              /*              */
       union {                                         /* ICDIPTR60    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TXI4:8;                    /*   TXI4       */
                    _UDWORD BRI5:8;                    /*   BRI5       */
                    _UDWORD ERI5:8;                    /*   ERI5       */
                    _UDWORD RXI5:8;                    /*   RXI5       */
                    } BIT;                             /*              */
             } ICDIPTR60;                              /*              */
       union {                                         /* ICDIPTR61    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TXI5:8;                    /*   TXI5       */
                    _UDWORD BRI6:8;                    /*   BRI6       */
                    _UDWORD ERI6:8;                    /*   ERI6       */
                    _UDWORD RXI6:8;                    /*   RXI6       */
                    } BIT;                             /*              */
             } ICDIPTR61;                              /*              */
       union {                                         /* ICDIPTR62    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TXI6:8;                    /*   TXI6       */
                    _UDWORD BRI7:8;                    /*   BRI7       */
                    _UDWORD ERI7:8;                    /*   ERI7       */
                    _UDWORD RXI7:8;                    /*   RXI7       */
                    } BIT;                             /*              */
             } ICDIPTR62;                              /*              */
       union {                                         /* ICDIPTR63    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TXI7:8;                    /*   TXI7       */
                    _UDWORD GERI:8;                    /*   GERI       */
                    _UDWORD RFI:8;                     /*   RFI        */
                    _UDWORD CFRXI0:8;                  /*   CFRXI0     */
                    } BIT;                             /*              */
             } ICDIPTR63;                              /*              */
       union {                                         /* ICDIPTR64    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CERI0:8;                   /*   CERI0      */
                    _UDWORD CTXI0:8;                   /*   CTXI0      */
                    _UDWORD CFRXI1:8;                  /*   CFRXI1     */
                    _UDWORD CERI1:8;                   /*   CERI1      */
                    } BIT;                             /*              */
             } ICDIPTR64;                              /*              */
       union {                                         /* ICDIPTR65    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CTXI1:8;                   /*   CTXI1      */
                    _UDWORD CFRXI2:8;                  /*   CFRXI2     */
                    _UDWORD CERI2:8;                   /*   CERI2      */
                    _UDWORD CTXI2:8;                   /*   CTXI2      */
                    } BIT;                             /*              */
             } ICDIPTR65;                              /*              */
       union {                                         /* ICDIPTR66    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CFRXI3:8;                  /*   CFRXI3     */
                    _UDWORD CERI3:8;                   /*   CERI3      */
                    _UDWORD CTXI3:8;                   /*   CTXI3      */
                    _UDWORD CFRXI4:8;                  /*   CFRXI4     */
                    } BIT;                             /*              */
             } ICDIPTR66;                              /*              */
       union {                                         /* ICDIPTR67    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CERI4:8;                   /*   CERI4      */
                    _UDWORD CTXI4:8;                   /*   CTXI4      */
                    _UDWORD SPEI0:8;                   /*   SPEI0      */
                    _UDWORD SPRI0:8;                   /*   SPRI0      */
                    } BIT;                             /*              */
             } ICDIPTR67;                              /*              */
       union {                                         /* ICDIPTR68    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SPTI0:8;                   /*   SPTI0      */
                    _UDWORD SPEI1:8;                   /*   SPEI1      */
                    _UDWORD SPRI1:8;                   /*   SPRI1      */
                    _UDWORD SPTI1:8;                   /*   SPTI1      */
                    } BIT;                             /*              */
             } ICDIPTR68;                              /*              */
       union {                                         /* ICDIPTR69    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SPEI2:8;                   /*   SPEI2      */
                    _UDWORD SPRI2:8;                   /*   SPRI2      */
                    _UDWORD SPTI2:8;                   /*   SPTI2      */
                    _UDWORD SPEI3:8;                   /*   SPEI3      */
                    } BIT;                             /*              */
             } ICDIPTR69;                              /*              */
       union {                                         /* ICDIPTR70    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SPRI3:8;                   /*   SPRI3      */
                    _UDWORD SPTI3:8;                   /*   SPTI3      */
                    _UDWORD SPEI4:8;                   /*   SPEI4      */
                    _UDWORD SPRI4:8;                   /*   SPRI4      */
                    } BIT;                             /*              */
             } ICDIPTR70;                              /*              */
       union {                                         /* ICDIPTR71    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SPTI4:8;                   /*   SPTI4      */
                    _UDWORD IEBBTD:8;                  /*   IEBBTD     */
                    _UDWORD IEBBTERR:8;                /*   IEBBTERR   */
                    _UDWORD IEBBTSTA:8;                /*   IEBBTSTA   */
                    } BIT;                             /*              */
             } ICDIPTR71;                              /*              */
       union {                                         /* ICDIPTR72    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD IEBBTV:8;                  /*   IEBBTV     */
                    _UDWORD ISY:8;                     /*   ISY        */
                    _UDWORD IERR:8;                    /*   IERR       */
                    _UDWORD ITARG:8;                   /*   ITARG      */
                    } BIT;                             /*              */
             } ICDIPTR72;                              /*              */
       union {                                         /* ICDIPTR73    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD ISEC:8;                    /*   ISEC       */
                    _UDWORD IBUF:8;                    /*   IBUF       */
                    _UDWORD IREADY:8;                  /*   IREADY     */
                    _UDWORD FLSTE:8;                   /*   FLSTE      */
                    } BIT;                             /*              */
             } ICDIPTR73;                              /*              */
       union {                                         /* ICDIPTR74    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD FLTENDI:8;                 /*   FLTENDI    */
                    _UDWORD FLTREQ0I:8;                /*   FLTREQ0I   */
                    _UDWORD FLTREQ1I:8;                /*   FLTREQ1I   */
                    _UDWORD MMC0:8;                    /*   MMC0       */
                    } BIT;                             /*              */
             } ICDIPTR74;                              /*              */
       union {                                         /* ICDIPTR75    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD MMC1:8;                    /*   MMC1       */
                    _UDWORD MMC2:8;                    /*   MMC2       */
                    _UDWORD SDHI0_3:8;                 /*   SDHI0_3    */
                    _UDWORD SDHI0_0:8;                 /*   SDHI0_0    */
                    } BIT;                             /*              */
             } ICDIPTR75;                              /*              */
       union {                                         /* ICDIPTR76    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SDHI0_1:8;                 /*   SDHI0_1    */
                    _UDWORD SDHI1_3:8;                 /*   SDHI1_3    */
                    _UDWORD SDHI1_0:8;                 /*   SDHI1_0    */
                    _UDWORD SDHI1_1:8;                 /*   SDHI1_1    */
                    } BIT;                             /*              */
             } ICDIPTR76;                              /*              */
       union {                                         /* ICDIPTR77    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD ARM:8;                     /*   ARM        */
                    _UDWORD PRD:8;                     /*   PRD        */
                    _UDWORD CUP:8;                     /*   CUP        */
                    _UDWORD SCUAI0:8;                  /*   SCUAI0     */
                    } BIT;                             /*              */
             } ICDIPTR77;                              /*              */
       union {                                         /* ICDIPTR78    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SCUAI1:8;                  /*   SCUAI1     */
                    _UDWORD SCUFDI0:8;                 /*   SCUFDI0    */
                    _UDWORD SCUFDI1:8;                 /*   SCUFDI1    */
                    _UDWORD SCUFDI2:8;                 /*   SCUFDI2    */
                    } BIT;                             /*              */
             } ICDIPTR78;                              /*              */
       union {                                         /* ICDIPTR79    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SCUFDI3:8;                 /*   SCUFDI3    */
                    _UDWORD SCUFUI0:8;                 /*   SCUFUI0    */
                    _UDWORD SCUFUI1:8;                 /*   SCUFUI1    */
                    _UDWORD SCUFUI2:8;                 /*   SCUFUI2    */
                    } BIT;                             /*              */
             } ICDIPTR79;                              /*              */
       union {                                         /* ICDIPTR80    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SCUFUI3:8;                 /*   SCUFUI3    */
                    _UDWORD SCUDVI0:8;                 /*   SCUDVI0    */
                    _UDWORD SCUDVI1:8;                 /*   SCUDVI1    */
                    _UDWORD SCUDVI2:8;                 /*   SCUDVI2    */
                    } BIT;                             /*              */
             } ICDIPTR80;                              /*              */
       union {                                         /* ICDIPTR81    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SCUDVI3:8;                 /*   SCUDVI3    */
                    _UDWORD MLBCI:8;                   /*   MLBCI      */
                    _UDWORD MLBSI:8;                   /*   MLBSI      */
                    _UDWORD DRC0:8;                    /*   DRC0       */
                    } BIT;                             /*              */
             } ICDIPTR81;                              /*              */
       union {                                         /* ICDIPTR82    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD DRC1:8;                    /*   DRC1       */
                    _UDWORD :16;                       /*              */
                    _UDWORD LINI0_INT_T:8;             /*   LINI0_INT_T */
                    } BIT;                             /*              */
             } ICDIPTR82;                              /*              */
       union {                                         /* ICDIPTR83    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD LINI0_INT_R:8;             /*   LINI0_INT_R */
                    _UDWORD LINI0_INT_S:8;             /*   LINI0_INT_S */
                    _UDWORD LINI0_INT_M:8;             /*   LINI0_INT_M */
                    _UDWORD LINI1_INT_T:8;             /*   LINI1_INT_T */
                    } BIT;                             /*              */
             } ICDIPTR83;                              /*              */
       union {                                         /* ICDIPTR84    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD LINI1_INT_R:8;             /*   LINI1_INT_R */
                    _UDWORD LINI1_INT_S:8;             /*   LINI1_INT_S */
                    _UDWORD LINI1_INT_M:8;             /*   LINI1_INT_M */
                    _UDWORD :8;                        /*              */
                    } BIT;                             /*              */
             } ICDIPTR84;                              /*              */
       _UBYTE wk15[4];                                 /*              */
       union {                                         /* ICDIPTR86    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :24;                       /*              */
                    _UDWORD ERI0:8;                    /*   ERI0       */
                    } BIT;                             /*              */
             } ICDIPTR86;                              /*              */
       union {                                         /* ICDIPTR87    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD RXI0:8;                    /*   RXI0       */
                    _UDWORD TXI0:8;                    /*   TXI0       */
                    _UDWORD TEI0:8;                    /*   TEI0       */
                    _UDWORD ERI1:8;                    /*   ERI1       */
                    } BIT;                             /*              */
             } ICDIPTR87;                              /*              */
       union {                                         /* ICDIPTR88    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD RXI1:8;                    /*   RXI1       */
                    _UDWORD TXI1:8;                    /*   TXI1       */
                    _UDWORD TEI1:8;                    /*   TEI1       */
                    _UDWORD :8;                        /*              */
                    } BIT;                             /*              */
             } ICDIPTR88;                              /*              */
       union {                                         /* ICDIPTR89    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :24;                       /*              */
                    _UDWORD ETHERI:8;                  /*   ETHERI     */
                    } BIT;                             /*              */
             } ICDIPTR89;                              /*              */
       _UBYTE wk16[4];                                 /*              */
       union {                                         /* ICDIPTR91    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD CEUI:8;                    /*   CEUI       */
                    _UDWORD INT_CSIH0TIR:8;            /*   INT_CSIH0TIR */
                    _UDWORD INT_CSIH0TIRE:8;           /*   INT_CSIH0TIRE */
                    _UDWORD INT_CSIH1TIC:8;            /*   INT_CSIH1TIC */
                    } BIT;                             /*              */
             } ICDIPTR91;                              /*              */
       union {                                         /* ICDIPTR92    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD INT_CSIH1TIJC:8;           /*   INT_CSIH1TIJC */
                    _UDWORD ECCE10:8;                  /*   ECCE10     */
                    _UDWORD ECCE20:8;                  /*   ECCE20     */
                    _UDWORD ECCOVF0:8;                 /*   ECCOVF0    */
                    } BIT;                             /*              */
             } ICDIPTR92;                              /*              */
       union {                                         /* ICDIPTR93    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD ECCE11:8;                  /*   ECCE11     */
                    _UDWORD ECCE21:8;                  /*   ECCE21     */
                    _UDWORD ECCOVF1:8;                 /*   ECCOVF1    */
                    _UDWORD ECCE12:8;                  /*   ECCE12     */
                    } BIT;                             /*              */
             } ICDIPTR93;                              /*              */
       union {                                         /* ICDIPTR94    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD ECCE22:8;                  /*   ECCE22     */
                    _UDWORD ECCOVF2:8;                 /*   ECCOVF2    */
                    _UDWORD ECCE13:8;                  /*   ECCE13     */
                    _UDWORD ECCE23:8;                  /*   ECCE23     */
                    } BIT;                             /*              */
             } ICDIPTR94;                              /*              */
       union {                                         /* ICDIPTR95    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD ECCOVF3:8;                 /*   ECCOVF3    */
                    _UDWORD H2XMLB_ERRINT:8;           /*   H2XMLB_ERRINT */
                    _UDWORD H2XIC1_ERRINT:8;           /*   H2XIC1_ERRINT */
                    _UDWORD X2HPERI1_ERRINT:8;         /*   X2HPERI1_ERRINT */
                    } BIT;                             /*              */
             } ICDIPTR95;                              /*              */
       union {                                         /* ICDIPTR96    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD X2HPERI2_ERRINT:8;         /*   X2HPERI2_ERRINT */
                    _UDWORD X2HPERI34_ERRINT:8;        /*   X2HPERI34_ERRINT */
                    _UDWORD X2HPERI5_ERRINT:8;         /*   X2HPERI5_ERRINT */
                    _UDWORD X2HPERI67_ERRINT:8;        /*   X2HPERI67_ERRINT */
                    } BIT;                             /*              */
             } ICDIPTR96;                              /*              */
       union {                                         /* ICDIPTR97    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD X2HDBGR_ERRINT:8;          /*   X2HDBGR_ERRINT */
                    _UDWORD PRRI:8;                    /*   PRRI       */
                    _UDWORD IFEI0:8;                   /*   IFEI0      */
                    _UDWORD OFFI0:8;                   /*   OFFI0      */
                    } BIT;                             /*              */
             } ICDIPTR97;                              /*              */
       union {                                         /* ICDIPTR98    */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD PFVEI0:8;                  /*   PFVEI0     */
                    _UDWORD IFEI1:8;                   /*   IFEI1      */
                    _UDWORD OFFI1:8;                   /*   OFFI1      */
                    _UDWORD PFVEI1:8;                  /*   PFVEI1     */
                    } BIT;                             /*              */
             } ICDIPTR98;                              /*              */
       _UBYTE wk17[20];                                /*              */
       union {                                         /* ICDIPTR104   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT0:8;                   /*   TINT0      */
                    _UDWORD TINT1:8;                   /*   TINT1      */
                    _UDWORD TINT2:8;                   /*   TINT2      */
                    _UDWORD TINT3:8;                   /*   TINT3      */
                    } BIT;                             /*              */
             } ICDIPTR104;                             /*              */
       union {                                         /* ICDIPTR105   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT4:8;                   /*   TINT4      */
                    _UDWORD TINT5:8;                   /*   TINT5      */
                    _UDWORD TINT6:8;                   /*   TINT6      */
                    _UDWORD TINT7:8;                   /*   TINT7      */
                    } BIT;                             /*              */
             } ICDIPTR105;                             /*              */
       union {                                         /* ICDIPTR106   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT8:8;                   /*   TINT8      */
                    _UDWORD TINT9:8;                   /*   TINT9      */
                    _UDWORD TINT10:8;                  /*   TINT10     */
                    _UDWORD TINT11:8;                  /*   TINT11     */
                    } BIT;                             /*              */
             } ICDIPTR106;                             /*              */
       union {                                         /* ICDIPTR107   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT12:8;                  /*   TINT12     */
                    _UDWORD TINT13:8;                  /*   TINT13     */
                    _UDWORD TINT14:8;                  /*   TINT14     */
                    _UDWORD TINT15:8;                  /*   TINT15     */
                    } BIT;                             /*              */
             } ICDIPTR107;                             /*              */
       union {                                         /* ICDIPTR108   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT16:8;                  /*   TINT16     */
                    _UDWORD TINT17:8;                  /*   TINT17     */
                    _UDWORD TINT18:8;                  /*   TINT18     */
                    _UDWORD TINT19:8;                  /*   TINT19     */
                    } BIT;                             /*              */
             } ICDIPTR108;                             /*              */
       union {                                         /* ICDIPTR109   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT20:8;                  /*   TINT20     */
                    _UDWORD TINT21:8;                  /*   TINT21     */
                    _UDWORD TINT22:8;                  /*   TINT22     */
                    _UDWORD TINT23:8;                  /*   TINT23     */
                    } BIT;                             /*              */
             } ICDIPTR109;                             /*              */
       union {                                         /* ICDIPTR110   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT24:8;                  /*   TINT24     */
                    _UDWORD TINT25:8;                  /*   TINT25     */
                    _UDWORD TINT26:8;                  /*   TINT26     */
                    _UDWORD TINT27:8;                  /*   TINT27     */
                    } BIT;                             /*              */
             } ICDIPTR110;                             /*              */
       union {                                         /* ICDIPTR111   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT28:8;                  /*   TINT28     */
                    _UDWORD TINT29:8;                  /*   TINT29     */
                    _UDWORD TINT30:8;                  /*   TINT30     */
                    _UDWORD TINT31:8;                  /*   TINT31     */
                    } BIT;                             /*              */
             } ICDIPTR111;                             /*              */
       union {                                         /* ICDIPTR112   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT32:8;                  /*   TINT32     */
                    _UDWORD TINT33:8;                  /*   TINT33     */
                    _UDWORD TINT34:8;                  /*   TINT34     */
                    _UDWORD TINT35:8;                  /*   TINT35     */
                    } BIT;                             /*              */
             } ICDIPTR112;                             /*              */
       union {                                         /* ICDIPTR113   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT36:8;                  /*   TINT36     */
                    _UDWORD TINT37:8;                  /*   TINT37     */
                    _UDWORD TINT38:8;                  /*   TINT38     */
                    _UDWORD TINT39:8;                  /*   TINT39     */
                    } BIT;                             /*              */
             } ICDIPTR113;                             /*              */
       union {                                         /* ICDIPTR114   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT40:8;                  /*   TINT40     */
                    _UDWORD TINT41:8;                  /*   TINT41     */
                    _UDWORD TINT42:8;                  /*   TINT42     */
                    _UDWORD TINT43:8;                  /*   TINT43     */
                    } BIT;                             /*              */
             } ICDIPTR114;                             /*              */
       union {                                         /* ICDIPTR115   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT44:8;                  /*   TINT44     */
                    _UDWORD TINT45:8;                  /*   TINT45     */
                    _UDWORD TINT46:8;                  /*   TINT46     */
                    _UDWORD TINT47:8;                  /*   TINT47     */
                    } BIT;                             /*              */
             } ICDIPTR115;                             /*              */
       union {                                         /* ICDIPTR116   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT48:8;                  /*   TINT48     */
                    _UDWORD TINT49:8;                  /*   TINT49     */
                    _UDWORD TINT50:8;                  /*   TINT50     */
                    _UDWORD TINT51:8;                  /*   TINT51     */
                    } BIT;                             /*              */
             } ICDIPTR116;                             /*              */
       union {                                         /* ICDIPTR117   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT52:8;                  /*   TINT52     */
                    _UDWORD TINT53:8;                  /*   TINT53     */
                    _UDWORD TINT54:8;                  /*   TINT54     */
                    _UDWORD TINT55:8;                  /*   TINT55     */
                    } BIT;                             /*              */
             } ICDIPTR117;                             /*              */
       union {                                         /* ICDIPTR118   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT56:8;                  /*   TINT56     */
                    _UDWORD TINT57:8;                  /*   TINT57     */
                    _UDWORD TINT58:8;                  /*   TINT58     */
                    _UDWORD TINT59:8;                  /*   TINT59     */
                    } BIT;                             /*              */
             } ICDIPTR118;                             /*              */
       union {                                         /* ICDIPTR119   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT60:8;                  /*   TINT60     */
                    _UDWORD TINT61:8;                  /*   TINT61     */
                    _UDWORD TINT62:8;                  /*   TINT62     */
                    _UDWORD TINT63:8;                  /*   TINT63     */
                    } BIT;                             /*              */
             } ICDIPTR119;                             /*              */
       union {                                         /* ICDIPTR120   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT64:8;                  /*   TINT64     */
                    _UDWORD TINT65:8;                  /*   TINT65     */
                    _UDWORD TINT66:8;                  /*   TINT66     */
                    _UDWORD TINT67:8;                  /*   TINT67     */
                    } BIT;                             /*              */
             } ICDIPTR120;                             /*              */
       union {                                         /* ICDIPTR121   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT68:8;                  /*   TINT68     */
                    _UDWORD TINT69:8;                  /*   TINT69     */
                    _UDWORD TINT70:8;                  /*   TINT70     */
                    _UDWORD TINT71:8;                  /*   TINT71     */
                    } BIT;                             /*              */
             } ICDIPTR121;                             /*              */
       union {                                         /* ICDIPTR122   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT72:8;                  /*   TINT72     */
                    _UDWORD TINT73:8;                  /*   TINT73     */
                    _UDWORD TINT74:8;                  /*   TINT74     */
                    _UDWORD TINT75:8;                  /*   TINT75     */
                    } BIT;                             /*              */
             } ICDIPTR122;                             /*              */
       union {                                         /* ICDIPTR123   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT76:8;                  /*   TINT76     */
                    _UDWORD TINT77:8;                  /*   TINT77     */
                    _UDWORD TINT78:8;                  /*   TINT78     */
                    _UDWORD TINT79:8;                  /*   TINT79     */
                    } BIT;                             /*              */
             } ICDIPTR123;                             /*              */
       union {                                         /* ICDIPTR124   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT80:8;                  /*   TINT80     */
                    _UDWORD TINT81:8;                  /*   TINT81     */
                    _UDWORD TINT82:8;                  /*   TINT82     */
                    _UDWORD TINT83:8;                  /*   TINT83     */
                    } BIT;                             /*              */
             } ICDIPTR124;                             /*              */
       union {                                         /* ICDIPTR125   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT84:8;                  /*   TINT84     */
                    _UDWORD TINT85:8;                  /*   TINT85     */
                    _UDWORD TINT86:8;                  /*   TINT86     */
                    _UDWORD TINT87:8;                  /*   TINT87     */
                    } BIT;                             /*              */
             } ICDIPTR125;                             /*              */
       union {                                         /* ICDIPTR126   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT88:8;                  /*   TINT88     */
                    _UDWORD TINT89:8;                  /*   TINT89     */
                    _UDWORD TINT90:8;                  /*   TINT90     */
                    _UDWORD TINT91:8;                  /*   TINT91     */
                    } BIT;                             /*              */
             } ICDIPTR126;                             /*              */
       union {                                         /* ICDIPTR127   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT92:8;                  /*   TINT92     */
                    _UDWORD TINT93:8;                  /*   TINT93     */
                    _UDWORD TINT94:8;                  /*   TINT94     */
                    _UDWORD TINT95:8;                  /*   TINT95     */
                    } BIT;                             /*              */
             } ICDIPTR127;                             /*              */
       union {                                         /* ICDIPTR128   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT96:8;                  /*   TINT96     */
                    _UDWORD TINT97:8;                  /*   TINT97     */
                    _UDWORD TINT98:8;                  /*   TINT98     */
                    _UDWORD TINT99:8;                  /*   TINT99     */
                    } BIT;                             /*              */
             } ICDIPTR128;                             /*              */
       union {                                         /* ICDIPTR129   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT100:8;                 /*   TINT100    */
                    _UDWORD TINT101:8;                 /*   TINT101    */
                    _UDWORD TINT102:8;                 /*   TINT102    */
                    _UDWORD TINT103:8;                 /*   TINT103    */
                    } BIT;                             /*              */
             } ICDIPTR129;                             /*              */
       union {                                         /* ICDIPTR130   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT104:8;                 /*   TINT104    */
                    _UDWORD TINT105:8;                 /*   TINT105    */
                    _UDWORD TINT106:8;                 /*   TINT106    */
                    _UDWORD TINT107:8;                 /*   TINT107    */
                    } BIT;                             /*              */
             } ICDIPTR130;                             /*              */
       union {                                         /* ICDIPTR131   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT108:8;                 /*   TINT108    */
                    _UDWORD TINT109:8;                 /*   TINT109    */
                    _UDWORD TINT110:8;                 /*   TINT110    */
                    _UDWORD TINT111:8;                 /*   TINT111    */
                    } BIT;                             /*              */
             } ICDIPTR131;                             /*              */
       union {                                         /* ICDIPTR132   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT112:8;                 /*   TINT112    */
                    _UDWORD TINT113:8;                 /*   TINT113    */
                    _UDWORD TINT114:8;                 /*   TINT114    */
                    _UDWORD TINT115:8;                 /*   TINT115    */
                    } BIT;                             /*              */
             } ICDIPTR132;                             /*              */
       union {                                         /* ICDIPTR133   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT116:8;                 /*   TINT116    */
                    _UDWORD TINT117:8;                 /*   TINT117    */
                    _UDWORD TINT118:8;                 /*   TINT118    */
                    _UDWORD TINT119:8;                 /*   TINT119    */
                    } BIT;                             /*              */
             } ICDIPTR133;                             /*              */
       union {                                         /* ICDIPTR134   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT120:8;                 /*   TINT120    */
                    _UDWORD TINT121:8;                 /*   TINT121    */
                    _UDWORD TINT122:8;                 /*   TINT122    */
                    _UDWORD TINT123:8;                 /*   TINT123    */
                    } BIT;                             /*              */
             } ICDIPTR134;                             /*              */
       union {                                         /* ICDIPTR135   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT124:8;                 /*   TINT124    */
                    _UDWORD TINT125:8;                 /*   TINT125    */
                    _UDWORD TINT126:8;                 /*   TINT126    */
                    _UDWORD TINT127:8;                 /*   TINT127    */
                    } BIT;                             /*              */
             } ICDIPTR135;                             /*              */
       union {                                         /* ICDIPTR136   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT128:8;                 /*   TINT128    */
                    _UDWORD TINT129:8;                 /*   TINT129    */
                    _UDWORD TINT130:8;                 /*   TINT130    */
                    _UDWORD TINT131:8;                 /*   TINT131    */
                    } BIT;                             /*              */
             } ICDIPTR136;                             /*              */
       union {                                         /* ICDIPTR137   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT132:8;                 /*   TINT132    */
                    _UDWORD TINT133:8;                 /*   TINT133    */
                    _UDWORD TINT134:8;                 /*   TINT134    */
                    _UDWORD TINT135:8;                 /*   TINT135    */
                    } BIT;                             /*              */
             } ICDIPTR137;                             /*              */
       union {                                         /* ICDIPTR138   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT136:8;                 /*   TINT136    */
                    _UDWORD TINT137:8;                 /*   TINT137    */
                    _UDWORD TINT138:8;                 /*   TINT138    */
                    _UDWORD TINT139:8;                 /*   TINT139    */
                    } BIT;                             /*              */
             } ICDIPTR138;                             /*              */
       union {                                         /* ICDIPTR139   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT140:8;                 /*   TINT140    */
                    _UDWORD TINT141:8;                 /*   TINT141    */
                    _UDWORD TINT142:8;                 /*   TINT142    */
                    _UDWORD TINT143:8;                 /*   TINT143    */
                    } BIT;                             /*              */
             } ICDIPTR139;                             /*              */
       union {                                         /* ICDIPTR140   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT144:8;                 /*   TINT144    */
                    _UDWORD TINT145:8;                 /*   TINT145    */
                    _UDWORD TINT146:8;                 /*   TINT146    */
                    _UDWORD TINT147:8;                 /*   TINT147    */
                    } BIT;                             /*              */
             } ICDIPTR140;                             /*              */
       union {                                         /* ICDIPTR141   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT148:8;                 /*   TINT148    */
                    _UDWORD TINT149:8;                 /*   TINT149    */
                    _UDWORD TINT150:8;                 /*   TINT150    */
                    _UDWORD TINT151:8;                 /*   TINT151    */
                    } BIT;                             /*              */
             } ICDIPTR141;                             /*              */
       union {                                         /* ICDIPTR142   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT152:8;                 /*   TINT152    */
                    _UDWORD TINT153:8;                 /*   TINT153    */
                    _UDWORD TINT154:8;                 /*   TINT154    */
                    _UDWORD TINT155:8;                 /*   TINT155    */
                    } BIT;                             /*              */
             } ICDIPTR142;                             /*              */
       union {                                         /* ICDIPTR143   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT156:8;                 /*   TINT156    */
                    _UDWORD TINT157:8;                 /*   TINT157    */
                    _UDWORD TINT158:8;                 /*   TINT158    */
                    _UDWORD TINT159:8;                 /*   TINT159    */
                    } BIT;                             /*              */
             } ICDIPTR143;                             /*              */
       union {                                         /* ICDIPTR144   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD TINT160:8;                 /*   TINT160    */
                    _UDWORD TINT161:8;                 /*   TINT161    */
                    _UDWORD TINT162:8;                 /*   TINT162    */
                    _UDWORD :8;                        /*              */
                    } BIT;                             /*              */
             } ICDIPTR144;                             /*              */
       _UBYTE wk18[444];                               /*              */
       union {                                         /* ICDICFR      */
             _UDWORD LONG[36];                         /*  Long Access */
             struct {                                  /*  ICDICFRn    */
                    union {                            /* ICDICFR0     */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD SW0_0:1;      /*   SW0[0]     */
                                 _UDWORD SW0_1:1;      /*   SW0[1]     */
                                 _UDWORD SW1_0:1;      /*   SW1[0]     */
                                 _UDWORD SW1_1:1;      /*   SW1[1]     */
                                 _UDWORD SW2_0:1;      /*   SW2[0]     */
                                 _UDWORD SW2_1:1;      /*   SW2[1]     */
                                 _UDWORD SW3_0:1;      /*   SW3[0]     */
                                 _UDWORD SW3_1:1;      /*   SW3[1]     */
                                 _UDWORD SW4_0:1;      /*   SW4[0]     */
                                 _UDWORD SW4_1:1;      /*   SW4[1]     */
                                 _UDWORD SW5_0:1;      /*   SW5[0]     */
                                 _UDWORD SW5_1:1;      /*   SW5[1]     */
                                 _UDWORD SW6_0:1;      /*   SW6[0]     */
                                 _UDWORD SW6_1:1;      /*   SW6[1]     */
                                 _UDWORD SW7_0:1;      /*   SW7[0]     */
                                 _UDWORD SW7_1:1;      /*   SW7[1]     */
                                 _UDWORD SW8_0:1;      /*   SW8[0]     */
                                 _UDWORD SW8_1:1;      /*   SW8[1]     */
                                 _UDWORD SW9_0:1;      /*   SW9[0]     */
                                 _UDWORD SW9_1:1;      /*   SW9[1]     */
                                 _UDWORD SW10_0:1;     /*   SW10[0]    */
                                 _UDWORD SW10_1:1;     /*   SW10[1]    */
                                 _UDWORD SW11_0:1;     /*   SW11[0]    */
                                 _UDWORD SW11_1:1;     /*   SW11[1]    */
                                 _UDWORD SW12_0:1;     /*   SW12[0]    */
                                 _UDWORD SW12_1:1;     /*   SW12[1]    */
                                 _UDWORD SW13_0:1;     /*   SW13[0]    */
                                 _UDWORD SW13_1:1;     /*   SW13[1]    */
                                 _UDWORD SW14_0:1;     /*   SW14[0]    */
                                 _UDWORD SW14_1:1;     /*   SW14[1]    */
                                 _UDWORD SW15_0:1;     /*   SW15[0]    */
                                 _UDWORD SW15_1:1;     /*   SW15[1]    */
                                 } BIT;                /*              */
                          } ICDICFR0;                  /*              */
                    union {                            /* ICDICFR1     */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD PMUIRQ0_0:1;  /*   PMUIRQ0[0] */
                                 _UDWORD PMUIRQ0_1:1;  /*   PMUIRQ0[1] */
                                 _UDWORD COMMRX0_0:1;  /*   COMMRX0[0] */
                                 _UDWORD COMMRX0_1:1;  /*   COMMRX0[1] */
                                 _UDWORD COMMTX0_0:1;  /*   COMMTX0[0] */
                                 _UDWORD COMMTX0_1:1;  /*   COMMTX0[1] */
                                 _UDWORD CTIIRQ0_0:1;  /*   CTIIRQ0[0] */
                                 _UDWORD CTIIRQ0_1:1;  /*   CTIIRQ0[1] */
                                 _UDWORD :24;          /*              */
                                 } BIT;                /*              */
                          } ICDICFR1;                  /*              */
                    union {                            /* ICDICFR2     */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD IRQ0_0:1;     /*   IRQ0[0]    */
                                 _UDWORD IRQ0_1:1;     /*   IRQ0[1]    */
                                 _UDWORD IRQ1_0:1;     /*   IRQ1[0]    */
                                 _UDWORD IRQ1_1:1;     /*   IRQ1[1]    */
                                 _UDWORD IRQ2_0:1;     /*   IRQ2[0]    */
                                 _UDWORD IRQ2_1:1;     /*   IRQ2[1]    */
                                 _UDWORD IRQ3_0:1;     /*   IRQ3[0]    */
                                 _UDWORD IRQ3_1:1;     /*   IRQ3[1]    */
                                 _UDWORD IRQ4_0:1;     /*   IRQ4[0]    */
                                 _UDWORD IRQ4_1:1;     /*   IRQ4[1]    */
                                 _UDWORD IRQ5_0:1;     /*   IRQ5[0]    */
                                 _UDWORD IRQ5_1:1;     /*   IRQ5[1]    */
                                 _UDWORD IRQ6_0:1;     /*   IRQ6[0]    */
                                 _UDWORD IRQ6_1:1;     /*   IRQ6[1]    */
                                 _UDWORD IRQ7_0:1;     /*   IRQ7[0]    */
                                 _UDWORD IRQ7_1:1;     /*   IRQ7[1]    */
                                 _UDWORD PL310ERR_0:1; /*   PL310ERR[0] */
                                 _UDWORD PL310ERR_1:1; /*   PL310ERR[1] */
                                 _UDWORD DMAINT0_0:1;  /*   DMAINT0[0] */
                                 _UDWORD DMAINT0_1:1;  /*   DMAINT0[1] */
                                 _UDWORD DMAINT1_0:1;  /*   DMAINT1[0] */
                                 _UDWORD DMAINT1_1:1;  /*   DMAINT1[1] */
                                 _UDWORD DMAINT2_0:1;  /*   DMAINT2[0] */
                                 _UDWORD DMAINT2_1:1;  /*   DMAINT2[1] */
                                 _UDWORD DMAINT3_0:1;  /*   DMAINT3[0] */
                                 _UDWORD DMAINT3_1:1;  /*   DMAINT3[1] */
                                 _UDWORD DMAINT4_0:1;  /*   DMAINT4[0] */
                                 _UDWORD DMAINT4_1:1;  /*   DMAINT4[1] */
                                 _UDWORD DMAINT5_0:1;  /*   DMAINT5[0] */
                                 _UDWORD DMAINT5_1:1;  /*   DMAINT5[1] */
                                 _UDWORD DMAINT6_0:1;  /*   DMAINT6[0] */
                                 _UDWORD DMAINT6_1:1;  /*   DMAINT6[1] */
                                 } BIT;                /*              */
                          } ICDICFR2;                  /*              */
                    union {                            /* ICDICFR3     */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD DMAINT7_0:1;  /*   DMAINT7[0] */
                                 _UDWORD DMAINT7_1:1;  /*   DMAINT7[1] */
                                 _UDWORD DMAINT8_0:1;  /*   DMAINT8[0] */
                                 _UDWORD DMAINT8_1:1;  /*   DMAINT8[1] */
                                 _UDWORD DMAINT9_0:1;  /*   DMAINT9[0] */
                                 _UDWORD DMAINT9_1:1;  /*   DMAINT9[1] */
                                 _UDWORD DMAINT10_0:1; /*   DMAINT10[0] */
                                 _UDWORD DMAINT10_1:1; /*   DMAINT10[1] */
                                 _UDWORD DMAINT11_0:1; /*   DMAINT11[0] */
                                 _UDWORD DMAINT11_1:1; /*   DMAINT11[1] */
                                 _UDWORD DMAINT12_0:1; /*   DMAINT12[0] */
                                 _UDWORD DMAINT12_1:1; /*   DMAINT12[1] */
                                 _UDWORD DMAINT13_0:1; /*   DMAINT13[0] */
                                 _UDWORD DMAINT13_1:1; /*   DMAINT13[1] */
                                 _UDWORD DMAINT14_0:1; /*   DMAINT14[0] */
                                 _UDWORD DMAINT14_1:1; /*   DMAINT14[1] */
                                 _UDWORD DMAINT15_0:1; /*   DMAINT15[0] */
                                 _UDWORD DMAINT15_1:1; /*   DMAINT15[1] */
                                 _UDWORD DMAERR_0:1;   /*   DMAERR[0]  */
                                 _UDWORD DMAERR_1:1;   /*   DMAERR[1]  */
                                 _UDWORD :12;          /*              */
                                 } BIT;                /*              */
                          } ICDICFR3;                  /*              */
                    union {                            /* ICDICFR4     */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD :18;          /*              */
                                 _UDWORD USBI0_0:1;    /*   USBI0[0]   */
                                 _UDWORD USBI0_1:1;    /*   USBI0[1]   */
                                 _UDWORD USBI1_0:1;    /*   USBI1[0]   */
                                 _UDWORD USBI1_1:1;    /*   USBI1[1]   */
                                 _UDWORD S0_VI_VSYNC0_0:1;/*   S0_VI_VSYNC0[0] */
                                 _UDWORD S0_VI_VSYNC0_1:1;/*   S0_VI_VSYNC0[1] */
                                 _UDWORD S0_LO_VSYNC0_0:1;/*   S0_LO_VSYNC0[0] */
                                 _UDWORD S0_LO_VSYNC0_1:1;/*   S0_LO_VSYNC0[1] */
                                 _UDWORD S0_VSYNCERR0_0:1;/*   S0_VSYNCERR0[0] */
                                 _UDWORD S0_VSYNCERR0_1:1;/*   S0_VSYNCERR0[1] */
                                 _UDWORD GR3_VLINE0_0:1;/*   GR3_VLINE0[0] */
                                 _UDWORD GR3_VLINE0_1:1;/*   GR3_VLINE0[1] */
                                 _UDWORD S0_VFIELD0_0:1;/*   S0_VFIELD0[0] */
                                 _UDWORD S0_VFIELD0_1:1;/*   S0_VFIELD0[1] */
                                 } BIT;                /*              */
                          } ICDICFR4;                  /*              */
                    union {                            /* ICDICFR5     */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD IV1_VBUFERR0_0:1;/*   IV1_VBUFERR0[0] */
                                 _UDWORD IV1_VBUFERR0_1:1;/*   IV1_VBUFERR0[1] */
                                 _UDWORD IV3_VBUFERR0_0:1;/*   IV3_VBUFERR0[0] */
                                 _UDWORD IV3_VBUFERR0_1:1;/*   IV3_VBUFERR0[1] */
                                 _UDWORD IV5_VBUFERR0_0:1;/*   IV5_VBUFERR0[0] */
                                 _UDWORD IV5_VBUFERR0_1:1;/*   IV5_VBUFERR0[1] */
                                 _UDWORD IV6_VBUFERR0_0:1;/*   IV6_VBUFERR0[0] */
                                 _UDWORD IV6_VBUFERR0_1:1;/*   IV6_VBUFERR0[1] */
                                 _UDWORD S0_WLINE0_0:1;/*   S0_WLINE0[0] */
                                 _UDWORD S0_WLINE0_1:1;/*   S0_WLINE0[1] */
                                 _UDWORD S1_VI_VSYNC0_0:1;/*   S1_VI_VSYNC0[0] */
                                 _UDWORD S1_VI_VSYNC0_1:1;/*   S1_VI_VSYNC0[1] */
                                 _UDWORD S1_LO_VSYNC0_0:1;/*   S1_LO_VSYNC0[0] */
                                 _UDWORD S1_LO_VSYNC0_1:1;/*   S1_LO_VSYNC0[1] */
                                 _UDWORD S1_VSYNCERR0_0:1;/*   S1_VSYNCERR0[0] */
                                 _UDWORD S1_VSYNCERR0_1:1;/*   S1_VSYNCERR0[1] */
                                 _UDWORD S1_VFIELD0_0:1;/*   S1_VFIELD0[0] */
                                 _UDWORD S1_VFIELD0_1:1;/*   S1_VFIELD0[1] */
                                 _UDWORD IV2_VBUFERR0_0:1;/*   IV2_VBUFERR0[0] */
                                 _UDWORD IV2_VBUFERR0_1:1;/*   IV2_VBUFERR0[1] */
                                 _UDWORD IV4_VBUFERR0_0:1;/*   IV4_VBUFERR0[0] */
                                 _UDWORD IV4_VBUFERR0_1:1;/*   IV4_VBUFERR0[1] */
                                 _UDWORD S1_WLINE0_0:1;/*   S1_WLINE0[0] */
                                 _UDWORD S1_WLINE0_1:1;/*   S1_WLINE0[1] */
                                 _UDWORD OIR_VI_VSYNC0_0:1;/*   OIR_VI_VSYNC0[0] */
                                 _UDWORD OIR_VI_VSYNC0_1:1;/*   OIR_VI_VSYNC0[1] */
                                 _UDWORD OIR_LO_VSYNC0_0:1;/*   OIR_LO_VSYNC0[0] */
                                 _UDWORD OIR_LO_VSYNC0_1:1;/*   OIR_LO_VSYNC0[1] */
                                 _UDWORD OIR_VSYNCERR0_0:1;/*   OIR_VSYNCERR0[0] */
                                 _UDWORD OIR_VSYNCERR0_1:1;/*   OIR_VSYNCERR0[1] */
                                 _UDWORD OIR_VFIELD0_0:1;/*   OIR_VFIELD0[0] */
                                 _UDWORD OIR_VFIELD0_1:1;/*   OIR_VFIELD0[1] */
                                 } BIT;                /*              */
                          } ICDICFR5;                  /*              */
                    union {                            /* ICDICFR6     */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD IV7_VBUFERR0_0:1;/*   IV7_VBUFERR0[0] */
                                 _UDWORD IV7_VBUFERR0_1:1;/*   IV7_VBUFERR0[1] */
                                 _UDWORD IV8_VBUFERR0_0:1;/*   IV8_VBUFERR0[0] */
                                 _UDWORD IV8_VBUFERR0_1:1;/*   IV8_VBUFERR0[1] */
                                 _UDWORD OIR_WLINE0_0:1;/*   OIR_WLINE0[0] */
                                 _UDWORD OIR_WLINE0_1:1;/*   OIR_WLINE0[1] */
                                 _UDWORD S0_VI_VSYNC1_0:1;/*   S0_VI_VSYNC1[0] */
                                 _UDWORD S0_VI_VSYNC1_1:1;/*   S0_VI_VSYNC1[1] */
                                 _UDWORD S0_LO_VSYNC1_0:1;/*   S0_LO_VSYNC1[0] */
                                 _UDWORD S0_LO_VSYNC1_1:1;/*   S0_LO_VSYNC1[1] */
                                 _UDWORD S0_VSYNCERR1_0:1;/*   S0_VSYNCERR1[0] */
                                 _UDWORD S0_VSYNCERR1_1:1;/*   S0_VSYNCERR1[1] */
                                 _UDWORD GR3_VLINE1_0:1;/*   GR3_VLINE1[0] */
                                 _UDWORD GR3_VLINE1_1:1;/*   GR3_VLINE1[1] */
                                 _UDWORD S0_VFIELD1_0:1;/*   S0_VFIELD1[0] */
                                 _UDWORD S0_VFIELD1_1:1;/*   S0_VFIELD1[1] */
                                 _UDWORD IV1_VBUFERR1_0:1;/*   IV1_VBUFERR1[0] */
                                 _UDWORD IV1_VBUFERR1_1:1;/*   IV1_VBUFERR1[1] */
                                 _UDWORD IV3_VBUFERR1_0:1;/*   IV3_VBUFERR1[0] */
                                 _UDWORD IV3_VBUFERR1_1:1;/*   IV3_VBUFERR1[1] */
                                 _UDWORD IV5_VBUFERR1_0:1;/*   IV5_VBUFERR1[0] */
                                 _UDWORD IV5_VBUFERR1_1:1;/*   IV5_VBUFERR1[1] */
                                 _UDWORD IV6_VBUFERR1_0:1;/*   IV6_VBUFERR1[0] */
                                 _UDWORD IV6_VBUFERR1_1:1;/*   IV6_VBUFERR1[1] */
                                 _UDWORD S0_WLINE1_0:1;/*   S0_WLINE1[0] */
                                 _UDWORD S0_WLINE1_1:1;/*   S0_WLINE1[1] */
                                 _UDWORD S1_VI_VSYNC1_0:1;/*   S1_VI_VSYNC1[0] */
                                 _UDWORD S1_VI_VSYNC1_1:1;/*   S1_VI_VSYNC1[1] */
                                 _UDWORD S1_LO_VSYNC1_0:1;/*   S1_LO_VSYNC1[0] */
                                 _UDWORD S1_LO_VSYNC1_1:1;/*   S1_LO_VSYNC1[1] */
                                 _UDWORD S1_VSYNCERR1_0:1;/*   S1_VSYNCERR1[0] */
                                 _UDWORD S1_VSYNCERR1_1:1;/*   S1_VSYNCERR1[1] */
                                 } BIT;                /*              */
                          } ICDICFR6;                  /*              */
                    union {                            /* ICDICFR7     */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD S1_VFIELD1_0:1;/*   S1_VFIELD1[0] */
                                 _UDWORD S1_VFIELD1_1:1;/*   S1_VFIELD1[1] */
                                 _UDWORD IV2_VBUFERR1_0:1;/*   IV2_VBUFERR1[0] */
                                 _UDWORD IV2_VBUFERR1_1:1;/*   IV2_VBUFERR1[1] */
                                 _UDWORD IV4_VBUFERR1_0:1;/*   IV4_VBUFERR1[0] */
                                 _UDWORD IV4_VBUFERR1_1:1;/*   IV4_VBUFERR1[1] */
                                 _UDWORD S1_WLINE1_0:1;/*   S1_WLINE1[0] */
                                 _UDWORD S1_WLINE1_1:1;/*   S1_WLINE1[1] */
                                 _UDWORD OIR_VI_VSYNC1_0:1;/*   OIR_VI_VSYNC1[0] */
                                 _UDWORD OIR_VI_VSYNC1_1:1;/*   OIR_VI_VSYNC1[1] */
                                 _UDWORD OIR_LO_VSYNC1_0:1;/*   OIR_LO_VSYNC1[0] */
                                 _UDWORD OIR_LO_VSYNC1_1:1;/*   OIR_LO_VSYNC1[1] */
                                 _UDWORD OIR_VLINE1_0:1;/*   OIR_VLINE1[0] */
                                 _UDWORD OIR_VLINE1_1:1;/*   OIR_VLINE1[1] */
                                 _UDWORD OIR_VFIELD1_0:1;/*   OIR_VFIELD1[0] */
                                 _UDWORD OIR_VFIELD1_1:1;/*   OIR_VFIELD1[1] */
                                 _UDWORD IV7_VBUFERR1_0:1;/*   IV7_VBUFERR1[0] */
                                 _UDWORD IV7_VBUFERR1_1:1;/*   IV7_VBUFERR1[1] */
                                 _UDWORD IV8_VBUFERR1_0:1;/*   IV8_VBUFERR1[0] */
                                 _UDWORD IV8_VBUFERR1_1:1;/*   IV8_VBUFERR1[1] */
                                 _UDWORD OIR_WLINE1_0:1;/*   OIR_WLINE1[0] */
                                 _UDWORD OIR_WLINE1_1:1;/*   OIR_WLINE1[1] */
                                 _UDWORD IMRDI_0:1;    /*   IMRDI[0]   */
                                 _UDWORD IMRDI_1:1;    /*   IMRDI[1]   */
                                 _UDWORD IMR2I0_0:1;   /*   IMR2I0[0]  */
                                 _UDWORD IMR2I0_1:1;   /*   IMR2I0[1]  */
                                 _UDWORD IMR2I1_0:1;   /*   IMR2I1[0]  */
                                 _UDWORD IMR2I1_1:1;   /*   IMR2I1[1]  */
                                 _UDWORD JEDI_0:1;     /*   JEDI[0]    */
                                 _UDWORD JEDI_1:1;     /*   JEDI[1]    */
                                 _UDWORD JDTI_0:1;     /*   JDTI[0]    */
                                 _UDWORD JDTI_1:1;     /*   JDTI[1]    */
                                 } BIT;                /*              */
                          } ICDICFR7;                  /*              */
                    union {                            /* ICDICFR8     */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD CMP0_0:1;     /*   CMP0[0]    */
                                 _UDWORD CMP0_1:1;     /*   CMP0[1]    */
                                 _UDWORD CMP1_0:1;     /*   CMP1[0]    */
                                 _UDWORD CMP1_1:1;     /*   CMP1[1]    */
                                 _UDWORD INT0_0:1;     /*   INT0[0]    */
                                 _UDWORD INT0_1:1;     /*   INT0[1]    */
                                 _UDWORD INT1_0:1;     /*   INT1[0]    */
                                 _UDWORD INT1_1:1;     /*   INT1[1]    */
                                 _UDWORD INT2_0:1;     /*   INT2[0]    */
                                 _UDWORD INT2_1:1;     /*   INT2[1]    */
                                 _UDWORD INT3_0:1;     /*   INT3[0]    */
                                 _UDWORD INT3_1:1;     /*   INT3[1]    */
                                 _UDWORD OSTMI0_0:1;   /*   OSTMI0[0]  */
                                 _UDWORD OSTMI0_1:1;   /*   OSTMI0[1]  */
                                 _UDWORD OSTMI1_0:1;   /*   OSTMI1[0]  */
                                 _UDWORD OSTMI1_1:1;   /*   OSTMI1[1]  */
                                 _UDWORD CMI_0:1;      /*   CMI[0]     */
                                 _UDWORD CMI_1:1;      /*   CMI[1]     */
                                 _UDWORD WTOUT_0:1;    /*   WTOUT[0]   */
                                 _UDWORD WTOUT_1:1;    /*   WTOUT[1]   */
                                 _UDWORD ITI_0:1;      /*   ITI[0]     */
                                 _UDWORD ITI_1:1;      /*   ITI[1]     */
                                 _UDWORD TGI0A_0:1;    /*   TGI0A[0]   */
                                 _UDWORD TGI0A_1:1;    /*   TGI0A[1]   */
                                 _UDWORD TGI0B_0:1;    /*   TGI0B[0]   */
                                 _UDWORD TGI0B_1:1;    /*   TGI0B[1]   */
                                 _UDWORD TGI0C_0:1;    /*   TGI0C[0]   */
                                 _UDWORD TGI0C_1:1;    /*   TGI0C[1]   */
                                 _UDWORD TGI0D_0:1;    /*   TGI0D[0]   */
                                 _UDWORD TGI0D_1:1;    /*   TGI0D[1]   */
                                 _UDWORD TGI0V_0:1;    /*   TGI0V[0]   */
                                 _UDWORD TGI0V_1:1;    /*   TGI0V[1]   */
                                 } BIT;                /*              */
                          } ICDICFR8;                  /*              */
                    union {                            /* ICDICFR9     */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD TGI0E_0:1;    /*   TGI0E[0]   */
                                 _UDWORD TGI0E_1:1;    /*   TGI0E[1]   */
                                 _UDWORD TGI0F_0:1;    /*   TGI0F[0]   */
                                 _UDWORD TGI0F_1:1;    /*   TGI0F[1]   */
                                 _UDWORD TGI1A_0:1;    /*   TGI1A[0]   */
                                 _UDWORD TGI1A_1:1;    /*   TGI1A[1]   */
                                 _UDWORD TGI1B_0:1;    /*   TGI1B[0]   */
                                 _UDWORD TGI1B_1:1;    /*   TGI1B[1]   */
                                 _UDWORD TGI1V_0:1;    /*   TGI1V[0]   */
                                 _UDWORD TGI1V_1:1;    /*   TGI1V[1]   */
                                 _UDWORD TGI1U_0:1;    /*   TGI1U[0]   */
                                 _UDWORD TGI1U_1:1;    /*   TGI1U[1]   */
                                 _UDWORD TGI2A_0:1;    /*   TGI2A[0]   */
                                 _UDWORD TGI2A_1:1;    /*   TGI2A[1]   */
                                 _UDWORD TGI2B_0:1;    /*   TGI2B[0]   */
                                 _UDWORD TGI2B_1:1;    /*   TGI2B[1]   */
                                 _UDWORD TGI2V_0:1;    /*   TGI2V[0]   */
                                 _UDWORD TGI2V_1:1;    /*   TGI2V[1]   */
                                 _UDWORD TGI2U_0:1;    /*   TGI2U[0]   */
                                 _UDWORD TGI2U_1:1;    /*   TGI2U[1]   */
                                 _UDWORD TGI3A_0:1;    /*   TGI3A[0]   */
                                 _UDWORD TGI3A_1:1;    /*   TGI3A[1]   */
                                 _UDWORD TGI3B_0:1;    /*   TGI3B[0]   */
                                 _UDWORD TGI3B_1:1;    /*   TGI3B[1]   */
                                 _UDWORD TGI3C_0:1;    /*   TGI3C[0]   */
                                 _UDWORD TGI3C_1:1;    /*   TGI3C[1]   */
                                 _UDWORD TGI3D_0:1;    /*   TGI3D[0]   */
                                 _UDWORD TGI3D_1:1;    /*   TGI3D[1]   */
                                 _UDWORD TGI3V_0:1;    /*   TGI3V[0]   */
                                 _UDWORD TGI3V_1:1;    /*   TGI3V[1]   */
                                 _UDWORD TGI4A_0:1;    /*   TGI4A[0]   */
                                 _UDWORD TGI4A_1:1;    /*   TGI4A[1]   */
                                 } BIT;                /*              */
                          } ICDICFR9;                  /*              */
                    union {                            /* ICDICFR10    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD TGI4B_0:1;    /*   TGI4B[0]   */
                                 _UDWORD TGI4B_1:1;    /*   TGI4B[1]   */
                                 _UDWORD TGI4C_0:1;    /*   TGI4C[0]   */
                                 _UDWORD TGI4C_1:1;    /*   TGI4C[1]   */
                                 _UDWORD TGI4D_0:1;    /*   TGI4D[0]   */
                                 _UDWORD TGI4D_1:1;    /*   TGI4D[1]   */
                                 _UDWORD TGI4V_0:1;    /*   TGI4V[0]   */
                                 _UDWORD TGI4V_1:1;    /*   TGI4V[1]   */
                                 _UDWORD CMI1_0:1;     /*   CMI1[0]    */
                                 _UDWORD CMI1_1:1;     /*   CMI1[1]    */
                                 _UDWORD CMI2_0:1;     /*   CMI2[0]    */
                                 _UDWORD CMI2_1:1;     /*   CMI2[1]    */
                                 _UDWORD SGDEI0_0:1;   /*   SGDEI0[0]  */
                                 _UDWORD SGDEI0_1:1;   /*   SGDEI0[1]  */
                                 _UDWORD SGDEI1_0:1;   /*   SGDEI1[0]  */
                                 _UDWORD SGDEI1_1:1;   /*   SGDEI1[1]  */
                                 _UDWORD SGDEI2_0:1;   /*   SGDEI2[0]  */
                                 _UDWORD SGDEI2_1:1;   /*   SGDEI2[1]  */
                                 _UDWORD SGDEI3_0:1;   /*   SGDEI3[0]  */
                                 _UDWORD SGDEI3_1:1;   /*   SGDEI3[1]  */
                                 _UDWORD ADI_0:1;      /*   ADI[0]     */
                                 _UDWORD ADI_1:1;      /*   ADI[1]     */
                                 _UDWORD ADWAR_0:1;    /*   ADWAR[0]   */
                                 _UDWORD ADWAR_1:1;    /*   ADWAR[1]   */
                                 _UDWORD SSII0_0:1;    /*   SSII0[0]   */
                                 _UDWORD SSII0_1:1;    /*   SSII0[1]   */
                                 _UDWORD SSIRXI0_0:1;  /*   SSIRXI0[0] */
                                 _UDWORD SSIRXI0_1:1;  /*   SSIRXI0[1] */
                                 _UDWORD SSITXI0_0:1;  /*   SSITXI0[0] */
                                 _UDWORD SSITXI0_1:1;  /*   SSITXI0[1] */
                                 _UDWORD SSII1_0:1;    /*   SSII1[0]   */
                                 _UDWORD SSII1_1:1;    /*   SSII1[1]   */
                                 } BIT;                /*              */
                          } ICDICFR10;                 /*              */
                    union {                            /* ICDICFR11    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD SSIRXI1_0:1;  /*   SSIRXI1[0] */
                                 _UDWORD SSIRXI1_1:1;  /*   SSIRXI1[1] */
                                 _UDWORD SSITXI1_0:1;  /*   SSITXI1[0] */
                                 _UDWORD SSITXI1_1:1;  /*   SSITXI1[1] */
                                 _UDWORD SSII2_0:1;    /*   SSII2[0]   */
                                 _UDWORD SSII2_1:1;    /*   SSII2[1]   */
                                 _UDWORD SSIRTI2_0:1;  /*   SSIRTI2[0] */
                                 _UDWORD SSIRTI2_1:1;  /*   SSIRTI2[1] */
                                 _UDWORD SSII3_0:1;    /*   SSII3[0]   */
                                 _UDWORD SSII3_1:1;    /*   SSII3[1]   */
                                 _UDWORD SSIRXI3_0:1;  /*   SSIRXI3[0] */
                                 _UDWORD SSIRXI3_1:1;  /*   SSIRXI3[1] */
                                 _UDWORD SSITXI3_0:1;  /*   SSITXI3[0] */
                                 _UDWORD SSITXI3_1:1;  /*   SSITXI3[1] */
                                 _UDWORD SSII4_0:1;    /*   SSII4[0]   */
                                 _UDWORD SSII4_1:1;    /*   SSII4[1]   */
                                 _UDWORD SSIRTI4_0:1;  /*   SSIRTI4[0] */
                                 _UDWORD SSIRTI4_1:1;  /*   SSIRTI4[1] */
                                 _UDWORD SSII5_0:1;    /*   SSII5[0]   */
                                 _UDWORD SSII5_1:1;    /*   SSII5[1]   */
                                 _UDWORD SSIRXI5_0:1;  /*   SSIRXI5[0] */
                                 _UDWORD SSIRXI5_1:1;  /*   SSIRXI5[1] */
                                 _UDWORD SSITXI5_0:1;  /*   SSITXI5[0] */
                                 _UDWORD SSITXI5_1:1;  /*   SSITXI5[1] */
                                 _UDWORD SPDIFI_0:1;   /*   SPDIFI[0]  */
                                 _UDWORD SPDIFI_1:1;   /*   SPDIFI[1]  */
                                 _UDWORD TEI0_0:1;     /*   TEI0[0]    */
                                 _UDWORD TEI0_1:1;     /*   TEI0[1]    */
                                 _UDWORD RI0_0:1;      /*   RI0[0]     */
                                 _UDWORD RI0_1:1;      /*   RI0[1]     */
                                 _UDWORD TI0_0:1;      /*   TI0[0]     */
                                 _UDWORD TI0_1:1;      /*   TI0[1]     */
                                 } BIT;                /*              */
                          } ICDICFR11;                 /*              */
                    union {                            /* ICDICFR12    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD SPI0_0:1;     /*   SPI0[0]    */
                                 _UDWORD SPI0_1:1;     /*   SPI0[1]    */
                                 _UDWORD STI0_0:1;     /*   STI0[0]    */
                                 _UDWORD STI0_1:1;     /*   STI0[1]    */
                                 _UDWORD NAKI0_0:1;    /*   NAKI0[0]   */
                                 _UDWORD NAKI0_1:1;    /*   NAKI0[1]   */
                                 _UDWORD ALI0_0:1;     /*   ALI0[0]    */
                                 _UDWORD ALI0_1:1;     /*   ALI0[1]    */
                                 _UDWORD TMOI0_0:1;    /*   TMOI0[0]   */
                                 _UDWORD TMOI0_1:1;    /*   TMOI0[1]   */
                                 _UDWORD TEI1_0:1;     /*   TEI1[0]    */
                                 _UDWORD TEI1_1:1;     /*   TEI1[1]    */
                                 _UDWORD RI1_0:1;      /*   RI1[0]     */
                                 _UDWORD RI1_1:1;      /*   RI1[1]     */
                                 _UDWORD TI1_0:1;      /*   TI1[0]     */
                                 _UDWORD TI1_1:1;      /*   TI1[1]     */
                                 _UDWORD SPI1_0:1;     /*   SPI1[0]    */
                                 _UDWORD SPI1_1:1;     /*   SPI1[1]    */
                                 _UDWORD STI1_0:1;     /*   STI1[0]    */
                                 _UDWORD STI1_1:1;     /*   STI1[1]    */
                                 _UDWORD NAKI1_0:1;    /*   NAKI1[0]   */
                                 _UDWORD NAKI1_1:1;    /*   NAKI1[1]   */
                                 _UDWORD ALI1_0:1;     /*   ALI1[0]    */
                                 _UDWORD ALI1_1:1;     /*   ALI1[1]    */
                                 _UDWORD TMOI1_0:1;    /*   TMOI1[0]   */
                                 _UDWORD TMOI1_1:1;    /*   TMOI1[1]   */
                                 _UDWORD TEI2_0:1;     /*   TEI2[0]    */
                                 _UDWORD TEI2_1:1;     /*   TEI2[1]    */
                                 _UDWORD RI2_0:1;      /*   RI2[0]     */
                                 _UDWORD RI2_1:1;      /*   RI2[1]     */
                                 _UDWORD TI2_0:1;      /*   TI2[0]     */
                                 _UDWORD TI2_1:1;      /*   TI2[1]     */
                                 } BIT;                /*              */
                          } ICDICFR12;                 /*              */
                    union {                            /* ICDICFR13    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD SPI2_0:1;     /*   SPI2[0]    */
                                 _UDWORD SPI2_1:1;     /*   SPI2[1]    */
                                 _UDWORD STI2_0:1;     /*   STI2[0]    */
                                 _UDWORD STI2_1:1;     /*   STI2[1]    */
                                 _UDWORD NAKI2_0:1;    /*   NAKI2[0]   */
                                 _UDWORD NAKI2_1:1;    /*   NAKI2[1]   */
                                 _UDWORD ALI2_0:1;     /*   ALI2[0]    */
                                 _UDWORD ALI2_1:1;     /*   ALI2[1]    */
                                 _UDWORD TMOI2_0:1;    /*   TMOI2[0]   */
                                 _UDWORD TMOI2_1:1;    /*   TMOI2[1]   */
                                 _UDWORD TEI3_0:1;     /*   TEI3[0]    */
                                 _UDWORD TEI3_1:1;     /*   TEI3[1]    */
                                 _UDWORD RI3_0:1;      /*   RI3[0]     */
                                 _UDWORD RI3_1:1;      /*   RI3[1]     */
                                 _UDWORD TI3_0:1;      /*   TI3[0]     */
                                 _UDWORD TI3_1:1;      /*   TI3[1]     */
                                 _UDWORD SPI3_0:1;     /*   SPI3[0]    */
                                 _UDWORD SPI3_1:1;     /*   SPI3[1]    */
                                 _UDWORD STI3_0:1;     /*   STI3[0]    */
                                 _UDWORD STI3_1:1;     /*   STI3[1]    */
                                 _UDWORD NAKI3_0:1;    /*   NAKI3[0]   */
                                 _UDWORD NAKI3_1:1;    /*   NAKI3[1]   */
                                 _UDWORD ALI3_0:1;     /*   ALI3[0]    */
                                 _UDWORD ALI3_1:1;     /*   ALI3[1]    */
                                 _UDWORD TMOI3_0:1;    /*   TMOI3[0]   */
                                 _UDWORD TMOI3_1:1;    /*   TMOI3[1]   */
                                 _UDWORD BRI0_0:1;     /*   BRI0[0]    */
                                 _UDWORD BRI0_1:1;     /*   BRI0[1]    */
                                 _UDWORD ERI0_0:1;     /*   ERI0[0]    */
                                 _UDWORD ERI0_1:1;     /*   ERI0[1]    */
                                 _UDWORD RXI0_0:1;     /*   RXI0[0]    */
                                 _UDWORD RXI0_1:1;     /*   RXI0[1]    */
                                 } BIT;                /*              */
                          } ICDICFR13;                 /*              */
                    union {                            /* ICDICFR14    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD TXI0_0:1;     /*   TXI0[0]    */
                                 _UDWORD TXI0_1:1;     /*   TXI0[1]    */
                                 _UDWORD BRI1_0:1;     /*   BRI1[0]    */
                                 _UDWORD BRI1_1:1;     /*   BRI1[1]    */
                                 _UDWORD ERI1_0:1;     /*   ERI1[0]    */
                                 _UDWORD ERI1_1:1;     /*   ERI1[1]    */
                                 _UDWORD RXI1_0:1;     /*   RXI1[0]    */
                                 _UDWORD RXI1_1:1;     /*   RXI1[1]    */
                                 _UDWORD TXI1_0:1;     /*   TXI1[0]    */
                                 _UDWORD TXI1_1:1;     /*   TXI1[1]    */
                                 _UDWORD BRI2_0:1;     /*   BRI2[0]    */
                                 _UDWORD BRI2_1:1;     /*   BRI2[1]    */
                                 _UDWORD ERI2_0:1;     /*   ERI2[0]    */
                                 _UDWORD ERI2_1:1;     /*   ERI2[1]    */
                                 _UDWORD RXI2_0:1;     /*   RXI2[0]    */
                                 _UDWORD RXI2_1:1;     /*   RXI2[1]    */
                                 _UDWORD TXI2_0:1;     /*   TXI2[0]    */
                                 _UDWORD TXI2_1:1;     /*   TXI2[1]    */
                                 _UDWORD BRI3_0:1;     /*   BRI3[0]    */
                                 _UDWORD BRI3_1:1;     /*   BRI3[1]    */
                                 _UDWORD ERI3_0:1;     /*   ERI3[0]    */
                                 _UDWORD ERI3_1:1;     /*   ERI3[1]    */
                                 _UDWORD RXI3_0:1;     /*   RXI3[0]    */
                                 _UDWORD RXI3_1:1;     /*   RXI3[1]    */
                                 _UDWORD TXI3_0:1;     /*   TXI3[0]    */
                                 _UDWORD TXI3_1:1;     /*   TXI3[1]    */
                                 _UDWORD BRI4_0:1;     /*   BRI4[0]    */
                                 _UDWORD BRI4_1:1;     /*   BRI4[1]    */
                                 _UDWORD ERI4_0:1;     /*   ERI4[0]    */
                                 _UDWORD ERI4_1:1;     /*   ERI4[1]    */
                                 _UDWORD RXI4_0:1;     /*   RXI4[0]    */
                                 _UDWORD RXI4_1:1;     /*   RXI4[1]    */
                                 } BIT;                /*              */
                          } ICDICFR14;                 /*              */
                    union {                            /* ICDICFR15    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD TXI4_0:1;     /*   TXI4[0]    */
                                 _UDWORD TXI4_1:1;     /*   TXI4[1]    */
                                 _UDWORD BRI5_0:1;     /*   BRI5[0]    */
                                 _UDWORD BRI5_1:1;     /*   BRI5[1]    */
                                 _UDWORD ERI5_0:1;     /*   ERI5[0]    */
                                 _UDWORD ERI5_1:1;     /*   ERI5[1]    */
                                 _UDWORD RXI5_0:1;     /*   RXI5[0]    */
                                 _UDWORD RXI5_1:1;     /*   RXI5[1]    */
                                 _UDWORD TXI5_0:1;     /*   TXI5[0]    */
                                 _UDWORD TXI5_1:1;     /*   TXI5[1]    */
                                 _UDWORD BRI6_0:1;     /*   BRI6[0]    */
                                 _UDWORD BRI6_1:1;     /*   BRI6[1]    */
                                 _UDWORD ERI6_0:1;     /*   ERI6[0]    */
                                 _UDWORD ERI6_1:1;     /*   ERI6[1]    */
                                 _UDWORD RXI6_0:1;     /*   RXI6[0]    */
                                 _UDWORD RXI6_1:1;     /*   RXI6[1]    */
                                 _UDWORD TXI6_0:1;     /*   TXI6[0]    */
                                 _UDWORD TXI6_1:1;     /*   TXI6[1]    */
                                 _UDWORD BRI7_0:1;     /*   BRI7[0]    */
                                 _UDWORD BRI7_1:1;     /*   BRI7[1]    */
                                 _UDWORD ERI7_0:1;     /*   ERI7[0]    */
                                 _UDWORD ERI7_1:1;     /*   ERI7[1]    */
                                 _UDWORD RXI7_0:1;     /*   RXI7[0]    */
                                 _UDWORD RXI7_1:1;     /*   RXI7[1]    */
                                 _UDWORD TXI7_0:1;     /*   TXI7[0]    */
                                 _UDWORD TXI7_1:1;     /*   TXI7[1]    */
                                 _UDWORD GERI_0:1;     /*   GERI[0]    */
                                 _UDWORD GERI_1:1;     /*   GERI[1]    */
                                 _UDWORD RFI_0:1;      /*   RFI[0]     */
                                 _UDWORD RFI_1:1;      /*   RFI[1]     */
                                 _UDWORD CFRXI0_0:1;   /*   CFRXI0[0]  */
                                 _UDWORD CFRXI0_1:1;   /*   CFRXI0[1]  */
                                 } BIT;                /*              */
                          } ICDICFR15;                 /*              */
                    union {                            /* ICDICFR16    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD CERI0_0:1;    /*   CERI0[0]   */
                                 _UDWORD CERI0_1:1;    /*   CERI0[1]   */
                                 _UDWORD CTXI0_0:1;    /*   CTXI0[0]   */
                                 _UDWORD CTXI0_1:1;    /*   CTXI0[1]   */
                                 _UDWORD CFRXI1_0:1;   /*   CFRXI1[0]  */
                                 _UDWORD CFRXI1_1:1;   /*   CFRXI1[1]  */
                                 _UDWORD CERI1_0:1;    /*   CERI1[0]   */
                                 _UDWORD CERI1_1:1;    /*   CERI1[1]   */
                                 _UDWORD CTXI1_0:1;    /*   CTXI1[0]   */
                                 _UDWORD CTXI1_1:1;    /*   CTXI1[1]   */
                                 _UDWORD CFRXI2_0:1;   /*   CFRXI2[0]  */
                                 _UDWORD CFRXI2_1:1;   /*   CFRXI2[1]  */
                                 _UDWORD CERI2_0:1;    /*   CERI2[0]   */
                                 _UDWORD CERI2_1:1;    /*   CERI2[1]   */
                                 _UDWORD CTXI2_0:1;    /*   CTXI2[0]   */
                                 _UDWORD CTXI2_1:1;    /*   CTXI2[1]   */
                                 _UDWORD CFRXI3_0:1;   /*   CFRXI3[0]  */
                                 _UDWORD CFRXI3_1:1;   /*   CFRXI3[1]  */
                                 _UDWORD CERI3_0:1;    /*   CERI3[0]   */
                                 _UDWORD CERI3_1:1;    /*   CERI3[1]   */
                                 _UDWORD CTXI3_0:1;    /*   CTXI3[0]   */
                                 _UDWORD CTXI3_1:1;    /*   CTXI3[1]   */
                                 _UDWORD CFRXI4_0:1;   /*   CFRXI4[0]  */
                                 _UDWORD CFRXI4_1:1;   /*   CFRXI4[1]  */
                                 _UDWORD CERI4_0:1;    /*   CERI4[0]   */
                                 _UDWORD CERI4_1:1;    /*   CERI4[1]   */
                                 _UDWORD CTXI4_0:1;    /*   CTXI4[0]   */
                                 _UDWORD CTXI4_1:1;    /*   CTXI4[1]   */
                                 _UDWORD SPEI0_0:1;    /*   SPEI0[0]   */
                                 _UDWORD SPEI0_1:1;    /*   SPEI0[1]   */
                                 _UDWORD SPRI0_0:1;    /*   SPRI0[0]   */
                                 _UDWORD SPRI0_1:1;    /*   SPRI0[1]   */
                                 } BIT;                /*              */
                          } ICDICFR16;                 /*              */
                    union {                            /* ICDICFR17    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD SPTI0_0:1;    /*   SPTI0[0]   */
                                 _UDWORD SPTI0_1:1;    /*   SPTI0[1]   */
                                 _UDWORD SPEI1_0:1;    /*   SPEI1[0]   */
                                 _UDWORD SPEI1_1:1;    /*   SPEI1[1]   */
                                 _UDWORD SPRI1_0:1;    /*   SPRI1[0]   */
                                 _UDWORD SPRI1_1:1;    /*   SPRI1[1]   */
                                 _UDWORD SPTI1_0:1;    /*   SPTI1[0]   */
                                 _UDWORD SPTI1_1:1;    /*   SPTI1[1]   */
                                 _UDWORD SPEI2_0:1;    /*   SPEI2[0]   */
                                 _UDWORD SPEI2_1:1;    /*   SPEI2[1]   */
                                 _UDWORD SPRI2_0:1;    /*   SPRI2[0]   */
                                 _UDWORD SPRI2_1:1;    /*   SPRI2[1]   */
                                 _UDWORD SPTI2_0:1;    /*   SPTI2[0]   */
                                 _UDWORD SPTI2_1:1;    /*   SPTI2[1]   */
                                 _UDWORD SPEI3_0:1;    /*   SPEI3[0]   */
                                 _UDWORD SPEI3_1:1;    /*   SPEI3[1]   */
                                 _UDWORD SPRI3_0:1;    /*   SPRI3[0]   */
                                 _UDWORD SPRI3_1:1;    /*   SPRI3[1]   */
                                 _UDWORD SPTI3_0:1;    /*   SPTI3[0]   */
                                 _UDWORD SPTI3_1:1;    /*   SPTI3[1]   */
                                 _UDWORD SPEI4_0:1;    /*   SPEI4[0]   */
                                 _UDWORD SPEI4_1:1;    /*   SPEI4[1]   */
                                 _UDWORD SPRI4_0:1;    /*   SPRI4[0]   */
                                 _UDWORD SPRI4_1:1;    /*   SPRI4[1]   */
                                 _UDWORD SPTI4_0:1;    /*   SPTI4[0]   */
                                 _UDWORD SPTI4_1:1;    /*   SPTI4[1]   */
                                 _UDWORD IEBBTD_0:1;   /*   IEBBTD[0]  */
                                 _UDWORD IEBBTD_1:1;   /*   IEBBTD[1]  */
                                 _UDWORD IEBBTERR_0:1; /*   IEBBTERR[0] */
                                 _UDWORD IEBBTERR_1:1; /*   IEBBTERR[1] */
                                 _UDWORD IEBBTSTA_0:1; /*   IEBBTSTA[0] */
                                 _UDWORD IEBBTSTA_1:1; /*   IEBBTSTA[1] */
                                 } BIT;                /*              */
                          } ICDICFR17;                 /*              */
                    union {                            /* ICDICFR18    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD IEBBTV_0:1;   /*   IEBBTV[0]  */
                                 _UDWORD IEBBTV_1:1;   /*   IEBBTV[1]  */
                                 _UDWORD ISY_0:1;      /*   ISY[0]     */
                                 _UDWORD ISY_1:1;      /*   ISY[1]     */
                                 _UDWORD IERR_0:1;     /*   IERR[0]    */
                                 _UDWORD IERR_1:1;     /*   IERR[1]    */
                                 _UDWORD ITARG_0:1;    /*   ITARG[0]   */
                                 _UDWORD ITARG_1:1;    /*   ITARG[1]   */
                                 _UDWORD ISEC_0:1;     /*   ISEC[0]    */
                                 _UDWORD ISEC_1:1;     /*   ISEC[1]    */
                                 _UDWORD IBUF_0:1;     /*   IBUF[0]    */
                                 _UDWORD IBUF_1:1;     /*   IBUF[1]    */
                                 _UDWORD IREADY_0:1;   /*   IREADY[0]  */
                                 _UDWORD IREADY_1:1;   /*   IREADY[1]  */
                                 _UDWORD FLSTE_0:1;    /*   FLSTE[0]   */
                                 _UDWORD FLSTE_1:1;    /*   FLSTE[1]   */
                                 _UDWORD FLTENDI_0:1;  /*   FLTENDI[0] */
                                 _UDWORD FLTENDI_1:1;  /*   FLTENDI[1] */
                                 _UDWORD FLTREQ0I_0:1; /*   FLTREQ0I[0] */
                                 _UDWORD FLTREQ0I_1:1; /*   FLTREQ0I[1] */
                                 _UDWORD FLTREQ1I_0:1; /*   FLTREQ1I[0] */
                                 _UDWORD FLTREQ1I_1:1; /*   FLTREQ1I[1] */
                                 _UDWORD MMC0_0:1;     /*   MMC0[0]    */
                                 _UDWORD MMC0_1:1;     /*   MMC0[1]    */
                                 _UDWORD MMC1_0:1;     /*   MMC1[0]    */
                                 _UDWORD MMC1_1:1;     /*   MMC1[1]    */
                                 _UDWORD MMC2_0:1;     /*   MMC2[0]    */
                                 _UDWORD MMC2_1:1;     /*   MMC2[1]    */
                                 _UDWORD SDHI0_3_0:1;  /*   SDHI0_3[0] */
                                 _UDWORD SDHI0_3_1:1;  /*   SDHI0_3[1] */
                                 _UDWORD SDHI0_0_0:1;  /*   SDHI0_0[0] */
                                 _UDWORD SDHI0_0_1:1;  /*   SDHI0_0[1] */
                                 } BIT;                /*              */
                          } ICDICFR18;                 /*              */
                    union {                            /* ICDICFR19    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD SDHI0_1_0:1;  /*   SDHI0_1[0] */
                                 _UDWORD SDHI0_1_1:1;  /*   SDHI0_1[1] */
                                 _UDWORD SDHI1_3_0:1;  /*   SDHI1_3[0] */
                                 _UDWORD SDHI1_3_1:1;  /*   SDHI1_3[1] */
                                 _UDWORD SDHI1_0_0:1;  /*   SDHI1_0[0] */
                                 _UDWORD SDHI1_0_1:1;  /*   SDHI1_0[1] */
                                 _UDWORD SDHI1_1_0:1;  /*   SDHI1_1[0] */
                                 _UDWORD SDHI1_1_1:1;  /*   SDHI1_1[1] */
                                 _UDWORD ARM_0:1;      /*   ARM[0]     */
                                 _UDWORD ARM_1:1;      /*   ARM[1]     */
                                 _UDWORD PRD_0:1;      /*   PRD[0]     */
                                 _UDWORD PRD_1:1;      /*   PRD[1]     */
                                 _UDWORD CUP_0:1;      /*   CUP[0]     */
                                 _UDWORD CUP_1:1;      /*   CUP[1]     */
                                 _UDWORD SCUAI0_0:1;   /*   SCUAI0[0]  */
                                 _UDWORD SCUAI0_1:1;   /*   SCUAI0[1]  */
                                 _UDWORD SCUAI1_0:1;   /*   SCUAI1[0]  */
                                 _UDWORD SCUAI1_1:1;   /*   SCUAI1[1]  */
                                 _UDWORD SCUFDI0_0:1;  /*   SCUFDI0[0] */
                                 _UDWORD SCUFDI0_1:1;  /*   SCUFDI0[1] */
                                 _UDWORD SCUFDI1_0:1;  /*   SCUFDI1[0] */
                                 _UDWORD SCUFDI1_1:1;  /*   SCUFDI1[1] */
                                 _UDWORD SCUFDI2_0:1;  /*   SCUFDI2[0] */
                                 _UDWORD SCUFDI2_1:1;  /*   SCUFDI2[1] */
                                 _UDWORD SCUFDI3_0:1;  /*   SCUFDI3[0] */
                                 _UDWORD SCUFDI3_1:1;  /*   SCUFDI3[1] */
                                 _UDWORD SCUFUI0_0:1;  /*   SCUFUI0[0] */
                                 _UDWORD SCUFUI0_1:1;  /*   SCUFUI0[1] */
                                 _UDWORD SCUFUI1_0:1;  /*   SCUFUI1[0] */
                                 _UDWORD SCUFUI1_1:1;  /*   SCUFUI1[1] */
                                 _UDWORD SCUFUI2_0:1;  /*   SCUFUI2[0] */
                                 _UDWORD SCUFUI2_1:1;  /*   SCUFUI2[1] */
                                 } BIT;                /*              */
                          } ICDICFR19;                 /*              */
                    union {                            /* ICDICFR20    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD SCUFUI3_0:1;  /*   SCUFUI3[0] */
                                 _UDWORD SCUFUI3_1:1;  /*   SCUFUI3[1] */
                                 _UDWORD SCUDVI0_0:1;  /*   SCUDVI0[0] */
                                 _UDWORD SCUDVI0_1:1;  /*   SCUDVI0[1] */
                                 _UDWORD SCUDVI1_0:1;  /*   SCUDVI1[0] */
                                 _UDWORD SCUDVI1_1:1;  /*   SCUDVI1[1] */
                                 _UDWORD SCUDVI2_0:1;  /*   SCUDVI2[0] */
                                 _UDWORD SCUDVI2_1:1;  /*   SCUDVI2[1] */
                                 _UDWORD SCUDVI3_0:1;  /*   SCUDVI3[0] */
                                 _UDWORD SCUDVI3_1:1;  /*   SCUDVI3[1] */
                                 _UDWORD MLBCI_0:1;    /*   MLBCI[0]   */
                                 _UDWORD MLBCI_1:1;    /*   MLBCI[1]   */
                                 _UDWORD MLBSI_0:1;    /*   MLBSI[0]   */
                                 _UDWORD MLBSI_1:1;    /*   MLBSI[1]   */
                                 _UDWORD DRC0_0:1;     /*   DRC0[0]    */
                                 _UDWORD DRC0_1:1;     /*   DRC0[1]    */
                                 _UDWORD DRC1_0:1;     /*   DRC1[0]    */
                                 _UDWORD DRC1_1:1;     /*   DRC1[1]    */
                                 _UDWORD :4;           /*              */
                                 _UDWORD LINI0_INT_T_0:1;/*   LINI0_INT_T[0] */
                                 _UDWORD LINI0_INT_T_1:1;/*   LINI0_INT_T[1] */
                                 _UDWORD LINI0_INT_R_0:1;/*   LINI0_INT_R[0] */
                                 _UDWORD LINI0_INT_R_1:1;/*   LINI0_INT_R[1] */
                                 _UDWORD LINI0_INT_S_0:1;/*   LINI0_INT_S[0] */
                                 _UDWORD LINI0_INT_S_1:1;/*   LINI0_INT_S[1] */
                                 _UDWORD LINI0_INT_M_0:1;/*   LINI0_INT_M[0] */
                                 _UDWORD LINI0_INT_M_1:1;/*   LINI0_INT_M[1] */
                                 _UDWORD LINI1_INT_T_0:1;/*   LINI1_INT_T[0] */
                                 _UDWORD LINI1_INT_T_1:1;/*   LINI1_INT_T[1] */
                                 } BIT;                /*              */
                          } ICDICFR20;                 /*              */
                    union {                            /* ICDICFR21    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD LINI1_INT_R_0:1;/*   LINI1_INT_R[0] */
                                 _UDWORD LINI1_INT_R_1:1;/*   LINI1_INT_R[1] */
                                 _UDWORD LINI1_INT_S_0:1;/*   LINI1_INT_S[0] */
                                 _UDWORD LINI1_INT_S_1:1;/*   LINI1_INT_S[1] */
                                 _UDWORD LINI1_INT_M_0:1;/*   LINI1_INT_M[0] */
                                 _UDWORD LINI1_INT_M_1:1;/*   LINI1_INT_M[1] */
                                 _UDWORD :16;          /*              */
                                 _UDWORD ERI0_0:1;     /*   ERI0[0]    */
                                 _UDWORD ERI0_1:1;     /*   ERI0[1]    */
                                 _UDWORD RXI0_0:1;     /*   RXI0[0]    */
                                 _UDWORD RXI0_1:1;     /*   RXI0[1]    */
                                 _UDWORD TXI0_0:1;     /*   TXI0[0]    */
                                 _UDWORD TXI0_1:1;     /*   TXI0[1]    */
                                 _UDWORD TEI0_0:1;     /*   TEI0[0]    */
                                 _UDWORD TEI0_1:1;     /*   TEI0[1]    */
                                 _UDWORD ERI1_0:1;     /*   ERI1[0]    */
                                 _UDWORD ERI1_1:1;     /*   ERI1[1]    */
                                 } BIT;                /*              */
                          } ICDICFR21;                 /*              */
                    union {                            /* ICDICFR22    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD RXI1_0:1;     /*   RXI1[0]    */
                                 _UDWORD RXI1_1:1;     /*   RXI1[1]    */
                                 _UDWORD TXI1_0:1;     /*   TXI1[0]    */
                                 _UDWORD TXI1_1:1;     /*   TXI1[1]    */
                                 _UDWORD TEI1_0:1;     /*   TEI1[0]    */
                                 _UDWORD TEI1_1:1;     /*   TEI1[1]    */
                                 _UDWORD :8;           /*              */
                                 _UDWORD ETHERI_0:1;   /*   ETHERI[0]  */
                                 _UDWORD ETHERI_1:1;   /*   ETHERI[1]  */
                                 _UDWORD :8;           /*              */
                                 _UDWORD CEUI_0:1;     /*   CEUI[0]    */
                                 _UDWORD CEUI_1:1;     /*   CEUI[1]    */
                                 _UDWORD INT_CSIH0TIR_0:1;/*   INT_CSIH0TIR[0] */
                                 _UDWORD INT_CSIH0TIR_1:1;/*   INT_CSIH0TIR[1] */
                                 _UDWORD INT_CSIH0TIRE_0:1;/*   INT_CSIH0TIRE[0] */
                                 _UDWORD INT_CSIH0TIRE_1:1;/*   INT_CSIH0TIRE[1] */
                                 _UDWORD INT_CSIH1TIC_0:1;/*   INT_CSIH1TIC[0] */
                                 _UDWORD INT_CSIH1TIC_1:1;/*   INT_CSIH1TIC[1] */
                                 } BIT;                /*              */
                          } ICDICFR22;                 /*              */
                    union {                            /* ICDICFR23    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD INT_CSIH1TIJC_0:1;/*   INT_CSIH1TIJC[0] */
                                 _UDWORD INT_CSIH1TIJC_1:1;/*   INT_CSIH1TIJC[1] */
                                 _UDWORD ECCE10_0:1;   /*   ECCE10[0]  */
                                 _UDWORD ECCE10_1:1;   /*   ECCE10[1]  */
                                 _UDWORD ECCE20_0:1;   /*   ECCE20[0]  */
                                 _UDWORD ECCE20_1:1;   /*   ECCE20[1]  */
                                 _UDWORD ECCOVF0_0:1;  /*   ECCOVF0[0] */
                                 _UDWORD ECCOVF0_1:1;  /*   ECCOVF0[1] */
                                 _UDWORD ECCE11_0:1;   /*   ECCE11[0]  */
                                 _UDWORD ECCE11_1:1;   /*   ECCE11[1]  */
                                 _UDWORD ECCE21_0:1;   /*   ECCE21[0]  */
                                 _UDWORD ECCE21_1:1;   /*   ECCE21[1]  */
                                 _UDWORD ECCOVF1_0:1;  /*   ECCOVF1[0] */
                                 _UDWORD ECCOVF1_1:1;  /*   ECCOVF1[1] */
                                 _UDWORD ECCE12_0:1;   /*   ECCE12[0]  */
                                 _UDWORD ECCE12_1:1;   /*   ECCE12[1]  */
                                 _UDWORD ECCE22_0:1;   /*   ECCE22[0]  */
                                 _UDWORD ECCE22_1:1;   /*   ECCE22[1]  */
                                 _UDWORD ECCOVF2_0:1;  /*   ECCOVF2[0] */
                                 _UDWORD ECCOVF2_1:1;  /*   ECCOVF2[1] */
                                 _UDWORD ECCE13_0:1;   /*   ECCE13[0]  */
                                 _UDWORD ECCE13_1:1;   /*   ECCE13[1]  */
                                 _UDWORD ECCE23_0:1;   /*   ECCE23[0]  */
                                 _UDWORD ECCE23_1:1;   /*   ECCE23[1]  */
                                 _UDWORD ECCOVF3_0:1;  /*   ECCOVF3[0] */
                                 _UDWORD ECCOVF3_1:1;  /*   ECCOVF3[1] */
                                 _UDWORD H2XMLB_ERRINT_0:1;/*   H2XMLB_ERRINT[0] */
                                 _UDWORD H2XMLB_ERRINT_1:1;/*   H2XMLB_ERRINT[1] */
                                 _UDWORD H2XIC1_ERRINT_0:1;/*   H2XIC1_ERRINT[0] */
                                 _UDWORD H2XIC1_ERRINT_1:1;/*   H2XIC1_ERRINT[1] */
                                 _UDWORD X2HPERI1_ERRINT_0:1;/*   X2HPERI1_ERRINT[0] */
                                 _UDWORD X2HPERI1_ERRINT_1:1;/*   X2HPERI1_ERRINT[1] */
                                 } BIT;                /*              */
                          } ICDICFR23;                 /*              */
                    union {                            /* ICDICFR24    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD X2HPERI2_ERRINT_0:1;/*   X2HPERI2_ERRINT[0] */
                                 _UDWORD X2HPERI2_ERRINT_1:1;/*   X2HPERI2_ERRINT[1] */
                                 _UDWORD X2HPERI34_ERRINT_0:1;/*   X2HPERI34_ERRINT[0] */
                                 _UDWORD X2HPERI34_ERRINT_1:1;/*   X2HPERI34_ERRINT[1] */
                                 _UDWORD X2HPERI5_ERRINT_0:1;/*   X2HPERI5_ERRINT[0] */
                                 _UDWORD X2HPERI5_ERRINT_1:1;/*   X2HPERI5_ERRINT[1] */
                                 _UDWORD X2HPERI67_ERRINT_0:1;/*   X2HPERI67_ERRINT[0] */
                                 _UDWORD X2HPERI67_ERRINT_1:1;/*   X2HPERI67_ERRINT[1] */
                                 _UDWORD X2HDBGR_ERRINT_0:1;/*   X2HDBGR_ERRINT[0] */
                                 _UDWORD X2HDBGR_ERRINT_1:1;/*   X2HDBGR_ERRINT[1] */
                                 _UDWORD PRRI_0:1;     /*   PRRI[0]    */
                                 _UDWORD PRRI_1:1;     /*   PRRI[1]    */
                                 _UDWORD IFEI0_0:1;    /*   IFEI0[0]   */
                                 _UDWORD IFEI0_1:1;    /*   IFEI0[1]   */
                                 _UDWORD OFFI0_0:1;    /*   OFFI0[0]   */
                                 _UDWORD OFFI0_1:1;    /*   OFFI0[1]   */
                                 _UDWORD PFVEI0_0:1;   /*   PFVEI0[0]  */
                                 _UDWORD PFVEI0_1:1;   /*   PFVEI0[1]  */
                                 _UDWORD IFEI1_0:1;    /*   IFEI1[0]   */
                                 _UDWORD IFEI1_1:1;    /*   IFEI1[1]   */
                                 _UDWORD OFFI1_0:1;    /*   OFFI1[0]   */
                                 _UDWORD OFFI1_1:1;    /*   OFFI1[1]   */
                                 _UDWORD PFVEI1_0:1;   /*   PFVEI1[0]  */
                                 _UDWORD PFVEI1_1:1;   /*   PFVEI1[1]  */
                                 _UDWORD :8;           /*              */
                                 } BIT;                /*              */
                          } ICDICFR24;                 /*              */
                    union {                            /* ICDICFR25    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD dummy:32;     /*              */
                                 } BIT;                /*              */
                          } ICDICFR25;                 /*              */
                    union {                            /* ICDICFR26    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD TINT0_0:1;    /*   TINT0[0]   */
                                 _UDWORD TINT0_1:1;    /*   TINT0[1]   */
                                 _UDWORD TINT1_0:1;    /*   TINT1[0]   */
                                 _UDWORD TINT1_1:1;    /*   TINT1[1]   */
                                 _UDWORD TINT2_0:1;    /*   TINT2[0]   */
                                 _UDWORD TINT2_1:1;    /*   TINT2[1]   */
                                 _UDWORD TINT3_0:1;    /*   TINT3[0]   */
                                 _UDWORD TINT3_1:1;    /*   TINT3[1]   */
                                 _UDWORD TINT4_0:1;    /*   TINT4[0]   */
                                 _UDWORD TINT4_1:1;    /*   TINT4[1]   */
                                 _UDWORD TINT5_0:1;    /*   TINT5[0]   */
                                 _UDWORD TINT5_1:1;    /*   TINT5[1]   */
                                 _UDWORD TINT6_0:1;    /*   TINT6[0]   */
                                 _UDWORD TINT6_1:1;    /*   TINT6[1]   */
                                 _UDWORD TINT7_0:1;    /*   TINT7[0]   */
                                 _UDWORD TINT7_1:1;    /*   TINT7[1]   */
                                 _UDWORD TINT8_0:1;    /*   TINT8[0]   */
                                 _UDWORD TINT8_1:1;    /*   TINT8[1]   */
                                 _UDWORD TINT9_0:1;    /*   TINT9[0]   */
                                 _UDWORD TINT9_1:1;    /*   TINT9[1]   */
                                 _UDWORD TINT10_0:1;   /*   TINT10[0]  */
                                 _UDWORD TINT10_1:1;   /*   TINT10[1]  */
                                 _UDWORD TINT11_0:1;   /*   TINT11[0]  */
                                 _UDWORD TINT11_1:1;   /*   TINT11[1]  */
                                 _UDWORD TINT12_0:1;   /*   TINT12[0]  */
                                 _UDWORD TINT12_1:1;   /*   TINT12[1]  */
                                 _UDWORD TINT13_0:1;   /*   TINT13[0]  */
                                 _UDWORD TINT13_1:1;   /*   TINT13[1]  */
                                 _UDWORD TINT14_0:1;   /*   TINT14[0]  */
                                 _UDWORD TINT14_1:1;   /*   TINT14[1]  */
                                 _UDWORD TINT15_0:1;   /*   TINT15[0]  */
                                 _UDWORD TINT15_1:1;   /*   TINT15[1]  */
                                 } BIT;                /*              */
                          } ICDICFR26;                 /*              */
                    union {                            /* ICDICFR27    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD TINT16_0:1;   /*   TINT16[0]  */
                                 _UDWORD TINT16_1:1;   /*   TINT16[1]  */
                                 _UDWORD TINT17_0:1;   /*   TINT17[0]  */
                                 _UDWORD TINT17_1:1;   /*   TINT17[1]  */
                                 _UDWORD TINT18_0:1;   /*   TINT18[0]  */
                                 _UDWORD TINT18_1:1;   /*   TINT18[1]  */
                                 _UDWORD TINT19_0:1;   /*   TINT19[0]  */
                                 _UDWORD TINT19_1:1;   /*   TINT19[1]  */
                                 _UDWORD TINT20_0:1;   /*   TINT20[0]  */
                                 _UDWORD TINT20_1:1;   /*   TINT20[1]  */
                                 _UDWORD TINT21_0:1;   /*   TINT21[0]  */
                                 _UDWORD TINT21_1:1;   /*   TINT21[1]  */
                                 _UDWORD TINT22_0:1;   /*   TINT22[0]  */
                                 _UDWORD TINT22_1:1;   /*   TINT22[1]  */
                                 _UDWORD TINT23_0:1;   /*   TINT23[0]  */
                                 _UDWORD TINT23_1:1;   /*   TINT23[1]  */
                                 _UDWORD TINT24_0:1;   /*   TINT24[0]  */
                                 _UDWORD TINT24_1:1;   /*   TINT24[1]  */
                                 _UDWORD TINT25_0:1;   /*   TINT25[0]  */
                                 _UDWORD TINT25_1:1;   /*   TINT25[1]  */
                                 _UDWORD TINT26_0:1;   /*   TINT26[0]  */
                                 _UDWORD TINT26_1:1;   /*   TINT26[1]  */
                                 _UDWORD TINT27_0:1;   /*   TINT27[0]  */
                                 _UDWORD TINT27_1:1;   /*   TINT27[1]  */
                                 _UDWORD TINT28_0:1;   /*   TINT28[0]  */
                                 _UDWORD TINT28_1:1;   /*   TINT28[1]  */
                                 _UDWORD TINT29_0:1;   /*   TINT29[0]  */
                                 _UDWORD TINT29_1:1;   /*   TINT29[1]  */
                                 _UDWORD TINT30_0:1;   /*   TINT30[0]  */
                                 _UDWORD TINT30_1:1;   /*   TINT30[1]  */
                                 _UDWORD TINT31_0:1;   /*   TINT31[0]  */
                                 _UDWORD TINT31_1:1;   /*   TINT31[1]  */
                                 } BIT;                /*              */
                          } ICDICFR27;                 /*              */
                    union {                            /* ICDICFR28    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD TINT32_0:1;   /*   TINT32[0]  */
                                 _UDWORD TINT32_1:1;   /*   TINT32[1]  */
                                 _UDWORD TINT33_0:1;   /*   TINT33[0]  */
                                 _UDWORD TINT33_1:1;   /*   TINT33[1]  */
                                 _UDWORD TINT34_0:1;   /*   TINT34[0]  */
                                 _UDWORD TINT34_1:1;   /*   TINT34[1]  */
                                 _UDWORD TINT35_0:1;   /*   TINT35[0]  */
                                 _UDWORD TINT35_1:1;   /*   TINT35[1]  */
                                 _UDWORD TINT36_0:1;   /*   TINT36[0]  */
                                 _UDWORD TINT36_1:1;   /*   TINT36[1]  */
                                 _UDWORD TINT37_0:1;   /*   TINT37[0]  */
                                 _UDWORD TINT37_1:1;   /*   TINT37[1]  */
                                 _UDWORD TINT38_0:1;   /*   TINT38[0]  */
                                 _UDWORD TINT38_1:1;   /*   TINT38[1]  */
                                 _UDWORD TINT39_0:1;   /*   TINT39[0]  */
                                 _UDWORD TINT39_1:1;   /*   TINT39[1]  */
                                 _UDWORD TINT40_0:1;   /*   TINT40[0]  */
                                 _UDWORD TINT40_1:1;   /*   TINT40[1]  */
                                 _UDWORD TINT41_0:1;   /*   TINT41[0]  */
                                 _UDWORD TINT41_1:1;   /*   TINT41[1]  */
                                 _UDWORD TINT42_0:1;   /*   TINT42[0]  */
                                 _UDWORD TINT42_1:1;   /*   TINT42[1]  */
                                 _UDWORD TINT43_0:1;   /*   TINT43[0]  */
                                 _UDWORD TINT43_1:1;   /*   TINT43[1]  */
                                 _UDWORD TINT44_0:1;   /*   TINT44[0]  */
                                 _UDWORD TINT44_1:1;   /*   TINT44[1]  */
                                 _UDWORD TINT45_0:1;   /*   TINT45[0]  */
                                 _UDWORD TINT45_1:1;   /*   TINT45[1]  */
                                 _UDWORD TINT46_0:1;   /*   TINT46[0]  */
                                 _UDWORD TINT46_1:1;   /*   TINT46[1]  */
                                 _UDWORD TINT47_0:1;   /*   TINT47[0]  */
                                 _UDWORD TINT47_1:1;   /*   TINT47[1]  */
                                 } BIT;                /*              */
                          } ICDICFR28;                 /*              */
                    union {                            /* ICDICFR29    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD TINT48_0:1;   /*   TINT48[0]  */
                                 _UDWORD TINT48_1:1;   /*   TINT48[1]  */
                                 _UDWORD TINT49_0:1;   /*   TINT49[0]  */
                                 _UDWORD TINT49_1:1;   /*   TINT49[1]  */
                                 _UDWORD TINT50_0:1;   /*   TINT50[0]  */
                                 _UDWORD TINT50_1:1;   /*   TINT50[1]  */
                                 _UDWORD TINT51_0:1;   /*   TINT51[0]  */
                                 _UDWORD TINT51_1:1;   /*   TINT51[1]  */
                                 _UDWORD TINT52_0:1;   /*   TINT52[0]  */
                                 _UDWORD TINT52_1:1;   /*   TINT52[1]  */
                                 _UDWORD TINT53_0:1;   /*   TINT53[0]  */
                                 _UDWORD TINT53_1:1;   /*   TINT53[1]  */
                                 _UDWORD TINT54_0:1;   /*   TINT54[0]  */
                                 _UDWORD TINT54_1:1;   /*   TINT54[1]  */
                                 _UDWORD TINT55_0:1;   /*   TINT55[0]  */
                                 _UDWORD TINT55_1:1;   /*   TINT55[1]  */
                                 _UDWORD TINT56_0:1;   /*   TINT56[0]  */
                                 _UDWORD TINT56_1:1;   /*   TINT56[1]  */
                                 _UDWORD TINT57_0:1;   /*   TINT57[0]  */
                                 _UDWORD TINT57_1:1;   /*   TINT57[1]  */
                                 _UDWORD TINT58_0:1;   /*   TINT58[0]  */
                                 _UDWORD TINT58_1:1;   /*   TINT58[1]  */
                                 _UDWORD TINT59_0:1;   /*   TINT59[0]  */
                                 _UDWORD TINT59_1:1;   /*   TINT59[1]  */
                                 _UDWORD TINT60_0:1;   /*   TINT60[0]  */
                                 _UDWORD TINT60_1:1;   /*   TINT60[1]  */
                                 _UDWORD TINT61_0:1;   /*   TINT61[0]  */
                                 _UDWORD TINT61_1:1;   /*   TINT61[1]  */
                                 _UDWORD TINT62_0:1;   /*   TINT62[0]  */
                                 _UDWORD TINT62_1:1;   /*   TINT62[1]  */
                                 _UDWORD TINT63_0:1;   /*   TINT63[0]  */
                                 _UDWORD TINT63_1:1;   /*   TINT63[1]  */
                                 } BIT;                /*              */
                          } ICDICFR29;                 /*              */
                    union {                            /* ICDICFR30    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD TINT64_0:1;   /*   TINT64[0]  */
                                 _UDWORD TINT64_1:1;   /*   TINT64[1]  */
                                 _UDWORD TINT65_0:1;   /*   TINT65[0]  */
                                 _UDWORD TINT65_1:1;   /*   TINT65[1]  */
                                 _UDWORD TINT66_0:1;   /*   TINT66[0]  */
                                 _UDWORD TINT66_1:1;   /*   TINT66[1]  */
                                 _UDWORD TINT67_0:1;   /*   TINT67[0]  */
                                 _UDWORD TINT67_1:1;   /*   TINT67[1]  */
                                 _UDWORD TINT68_0:1;   /*   TINT68[0]  */
                                 _UDWORD TINT68_1:1;   /*   TINT68[1]  */
                                 _UDWORD TINT69_0:1;   /*   TINT69[0]  */
                                 _UDWORD TINT69_1:1;   /*   TINT69[1]  */
                                 _UDWORD TINT70_0:1;   /*   TINT70[0]  */
                                 _UDWORD TINT70_1:1;   /*   TINT70[1]  */
                                 _UDWORD TINT71_0:1;   /*   TINT71[0]  */
                                 _UDWORD TINT71_1:1;   /*   TINT71[1]  */
                                 _UDWORD TINT72_0:1;   /*   TINT72[0]  */
                                 _UDWORD TINT72_1:1;   /*   TINT72[1]  */
                                 _UDWORD TINT73_0:1;   /*   TINT73[0]  */
                                 _UDWORD TINT73_1:1;   /*   TINT73[1]  */
                                 _UDWORD :12;          /*              */
                                 } BIT;                /*              */
                          } ICDICFR30;                 /*              */
                    union {                            /* ICDICFR31    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD TINT80_0:1;   /*   TINT80[0]  */
                                 _UDWORD TINT80_1:1;   /*   TINT80[1]  */
                                 _UDWORD TINT81_0:1;   /*   TINT81[0]  */
                                 _UDWORD TINT81_1:1;   /*   TINT81[1]  */
                                 _UDWORD TINT82_0:1;   /*   TINT82[0]  */
                                 _UDWORD TINT82_1:1;   /*   TINT82[1]  */
                                 _UDWORD TINT83_0:1;   /*   TINT83[0]  */
                                 _UDWORD TINT83_1:1;   /*   TINT83[1]  */
                                 _UDWORD TINT84_0:1;   /*   TINT84[0]  */
                                 _UDWORD TINT84_1:1;   /*   TINT84[1]  */
                                 _UDWORD TINT85_0:1;   /*   TINT85[0]  */
                                 _UDWORD TINT85_1:1;   /*   TINT85[1]  */
                                 _UDWORD TINT86_0:1;   /*   TINT86[0]  */
                                 _UDWORD TINT86_1:1;   /*   TINT86[1]  */
                                 _UDWORD TINT87_0:1;   /*   TINT87[0]  */
                                 _UDWORD TINT87_1:1;   /*   TINT87[1]  */
                                 _UDWORD TINT88_0:1;   /*   TINT88[0]  */
                                 _UDWORD TINT88_1:1;   /*   TINT88[1]  */
                                 _UDWORD TINT89_0:1;   /*   TINT89[0]  */
                                 _UDWORD TINT89_1:1;   /*   TINT89[1]  */
                                 _UDWORD TINT90_0:1;   /*   TINT90[0]  */
                                 _UDWORD TINT90_1:1;   /*   TINT90[1]  */
                                 _UDWORD TINT91_0:1;   /*   TINT91[0]  */
                                 _UDWORD TINT91_1:1;   /*   TINT91[1]  */
                                 _UDWORD TINT92_0:1;   /*   TINT92[0]  */
                                 _UDWORD TINT92_1:1;   /*   TINT92[1]  */
                                 _UDWORD TINT93_0:1;   /*   TINT93[0]  */
                                 _UDWORD TINT93_1:1;   /*   TINT93[1]  */
                                 _UDWORD TINT94_0:1;   /*   TINT94[0]  */
                                 _UDWORD TINT94_1:1;   /*   TINT94[1]  */
                                 _UDWORD TINT95_0:1;   /*   TINT95[0]  */
                                 _UDWORD TINT95_1:1;   /*   TINT95[1]  */
                                 } BIT;                /*              */
                          } ICDICFR31;                 /*              */
                    union {                            /* ICDICFR32    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD TINT96_0:1;   /*   TINT96[0]  */
                                 _UDWORD TINT96_1:1;   /*   TINT96[1]  */
                                 _UDWORD TINT97_0:1;   /*   TINT97[0]  */
                                 _UDWORD TINT97_1:1;   /*   TINT97[1]  */
                                 _UDWORD TINT98_0:1;   /*   TINT98[0]  */
                                 _UDWORD TINT98_1:1;   /*   TINT98[1]  */
                                 _UDWORD TINT99_0:1;   /*   TINT99[0]  */
                                 _UDWORD TINT99_1:1;   /*   TINT99[1]  */
                                 _UDWORD TINT100_0:1;  /*   TINT100[0] */
                                 _UDWORD TINT100_1:1;  /*   TINT100[1] */
                                 _UDWORD TINT101_0:1;  /*   TINT101[0] */
                                 _UDWORD TINT101_1:1;  /*   TINT101[1] */
                                 _UDWORD TINT102_0:1;  /*   TINT102[0] */
                                 _UDWORD TINT102_1:1;  /*   TINT102[1] */
                                 _UDWORD TINT103_0:1;  /*   TINT103[0] */
                                 _UDWORD TINT103_1:1;  /*   TINT103[1] */
                                 _UDWORD TINT104_0:1;  /*   TINT104[0] */
                                 _UDWORD TINT104_1:1;  /*   TINT104[1] */
                                 _UDWORD TINT105_0:1;  /*   TINT105[0] */
                                 _UDWORD TINT105_1:1;  /*   TINT105[1] */
                                 _UDWORD TINT106_0:1;  /*   TINT106[0] */
                                 _UDWORD TINT106_1:1;  /*   TINT106[1] */
                                 _UDWORD TINT107_0:1;  /*   TINT107[0] */
                                 _UDWORD TINT107_1:1;  /*   TINT107[1] */
                                 _UDWORD TINT108_0:1;  /*   TINT108[0] */
                                 _UDWORD TINT108_1:1;  /*   TINT108[1] */
                                 _UDWORD TINT109_0:1;  /*   TINT109[0] */
                                 _UDWORD TINT109_1:1;  /*   TINT109[1] */
                                 _UDWORD TINT110_0:1;  /*   TINT110[0] */
                                 _UDWORD TINT110_1:1;  /*   TINT110[1] */
                                 _UDWORD TINT111_0:1;  /*   TINT111[0] */
                                 _UDWORD TINT111_1:1;  /*   TINT111[1] */
                                 } BIT;                /*              */
                          } ICDICFR32;                 /*              */
                    union {                            /* ICDICFR33    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD TINT112_0:1;  /*   TINT112[0] */
                                 _UDWORD TINT112_1:1;  /*   TINT112[1] */
                                 _UDWORD TINT113_0:1;  /*   TINT113[0] */
                                 _UDWORD TINT113_1:1;  /*   TINT113[1] */
                                 _UDWORD TINT114_0:1;  /*   TINT114[0] */
                                 _UDWORD TINT114_1:1;  /*   TINT114[1] */
                                 _UDWORD TINT115_0:1;  /*   TINT115[0] */
                                 _UDWORD TINT115_1:1;  /*   TINT115[1] */
                                 _UDWORD TINT116_0:1;  /*   TINT116[0] */
                                 _UDWORD TINT116_1:1;  /*   TINT116[1] */
                                 _UDWORD TINT117_0:1;  /*   TINT117[0] */
                                 _UDWORD TINT117_1:1;  /*   TINT117[1] */
                                 _UDWORD TINT118_0:1;  /*   TINT118[0] */
                                 _UDWORD TINT118_1:1;  /*   TINT118[1] */
                                 _UDWORD TINT119_0:1;  /*   TINT119[0] */
                                 _UDWORD TINT119_1:1;  /*   TINT119[1] */
                                 _UDWORD TINT120_0:1;  /*   TINT120[0] */
                                 _UDWORD TINT120_1:1;  /*   TINT120[1] */
                                 _UDWORD TINT121_0:1;  /*   TINT121[0] */
                                 _UDWORD TINT121_1:1;  /*   TINT121[1] */
                                 _UDWORD TINT122_0:1;  /*   TINT122[0] */
                                 _UDWORD TINT122_1:1;  /*   TINT122[1] */
                                 _UDWORD TINT123_0:1;  /*   TINT123[0] */
                                 _UDWORD TINT123_1:1;  /*   TINT123[1] */
                                 _UDWORD TINT124_0:1;  /*   TINT124[0] */
                                 _UDWORD TINT124_1:1;  /*   TINT124[1] */
                                 _UDWORD TINT125_0:1;  /*   TINT125[0] */
                                 _UDWORD TINT125_1:1;  /*   TINT125[1] */
                                 _UDWORD TINT126_0:1;  /*   TINT126[0] */
                                 _UDWORD TINT126_1:1;  /*   TINT126[1] */
                                 _UDWORD TINT127_0:1;  /*   TINT127[0] */
                                 _UDWORD TINT127_1:1;  /*   TINT127[1] */
                                 } BIT;                /*              */
                          } ICDICFR33;                 /*              */
                    union {                            /* ICDICFR34    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD TINT128_0:1;  /*   TINT128[0] */
                                 _UDWORD TINT128_1:1;  /*   TINT128[1] */
                                 _UDWORD TINT129_0:1;  /*   TINT129[0] */
                                 _UDWORD TINT129_1:1;  /*   TINT129[1] */
                                 _UDWORD TINT130_0:1;  /*   TINT130[0] */
                                 _UDWORD TINT130_1:1;  /*   TINT130[1] */
                                 _UDWORD TINT131_0:1;  /*   TINT131[0] */
                                 _UDWORD TINT131_1:1;  /*   TINT131[1] */
                                 _UDWORD TINT132_0:1;  /*   TINT132[0] */
                                 _UDWORD TINT132_1:1;  /*   TINT132[1] */
                                 _UDWORD TINT133_0:1;  /*   TINT133[0] */
                                 _UDWORD TINT133_1:1;  /*   TINT133[1] */
                                 _UDWORD TINT134_0:1;  /*   TINT134[0] */
                                 _UDWORD TINT134_1:1;  /*   TINT134[1] */
                                 _UDWORD TINT135_0:1;  /*   TINT135[0] */
                                 _UDWORD TINT135_1:1;  /*   TINT135[1] */
                                 _UDWORD TINT136_0:1;  /*   TINT136[0] */
                                 _UDWORD TINT136_1:1;  /*   TINT136[1] */
                                 _UDWORD TINT137_0:1;  /*   TINT137[0] */
                                 _UDWORD TINT137_1:1;  /*   TINT137[1] */
                                 _UDWORD TINT138_0:1;  /*   TINT138[0] */
                                 _UDWORD TINT138_1:1;  /*   TINT138[1] */
                                 _UDWORD TINT139_0:1;  /*   TINT139[0] */
                                 _UDWORD TINT139_1:1;  /*   TINT139[1] */
                                 _UDWORD TINT140_0:1;  /*   TINT140[0] */
                                 _UDWORD TINT140_1:1;  /*   TINT140[1] */
                                 _UDWORD TINT141_0:1;  /*   TINT141[0] */
                                 _UDWORD TINT141_1:1;  /*   TINT141[1] */
                                 _UDWORD TINT142_0:1;  /*   TINT142[0] */
                                 _UDWORD TINT142_1:1;  /*   TINT142[1] */
                                 _UDWORD TINT143_0:1;  /*   TINT143[0] */
                                 _UDWORD TINT143_1:1;  /*   TINT143[1] */
                                 } BIT;                /*              */
                          } ICDICFR34;                 /*              */
                    union {                            /* ICDICFR35    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD TINT144_0:1;  /*   TINT144[0] */
                                 _UDWORD TINT144_1:1;  /*   TINT144[1] */
                                 _UDWORD TINT145_0:1;  /*   TINT145[0] */
                                 _UDWORD TINT145_1:1;  /*   TINT145[1] */
                                 _UDWORD TINT146_0:1;  /*   TINT146[0] */
                                 _UDWORD TINT146_1:1;  /*   TINT146[1] */
                                 _UDWORD TINT147_0:1;  /*   TINT147[0] */
                                 _UDWORD TINT147_1:1;  /*   TINT147[1] */
                                 _UDWORD TINT148_0:1;  /*   TINT148[0] */
                                 _UDWORD TINT148_1:1;  /*   TINT148[1] */
                                 _UDWORD TINT149_0:1;  /*   TINT149[0] */
                                 _UDWORD TINT149_1:1;  /*   TINT149[1] */
                                 _UDWORD TINT150_0:1;  /*   TINT150[0] */
                                 _UDWORD TINT150_1:1;  /*   TINT150[1] */
                                 _UDWORD TINT151_0:1;  /*   TINT151[0] */
                                 _UDWORD TINT151_1:1;  /*   TINT151[1] */
                                 _UDWORD TINT152_0:1;  /*   TINT152[0] */
                                 _UDWORD TINT152_1:1;  /*   TINT152[1] */
                                 _UDWORD TINT153_0:1;  /*   TINT153[0] */
                                 _UDWORD TINT153_1:1;  /*   TINT153[1] */
                                 _UDWORD TINT154_0:1;  /*   TINT154[0] */
                                 _UDWORD TINT154_1:1;  /*   TINT154[1] */
                                 _UDWORD TINT155_0:1;  /*   TINT155[0] */
                                 _UDWORD TINT155_1:1;  /*   TINT155[1] */
                                 _UDWORD TINT156_0:1;  /*   TINT156[0] */
                                 _UDWORD TINT156_1:1;  /*   TINT156[1] */
                                 _UDWORD TINT157_0:1;  /*   TINT157[0] */
                                 _UDWORD TINT157_1:1;  /*   TINT157[1] */
                                 _UDWORD TINT158_0:1;  /*   TINT158[0] */
                                 _UDWORD TINT158_1:1;  /*   TINT158[1] */
                                 _UDWORD TINT159_0:1;  /*   TINT159[0] */
                                 _UDWORD TINT159_1:1;  /*   TINT159[1] */
                                 } BIT;                /*              */
                          } ICDICFR35;                 /*              */
                    union {                            /* ICDICFR36    */
                          _UDWORD LONG;                /*  Long Access */
                          struct {                     /*  Bit Access  */
                                 _UDWORD TINT160_0:1;  /*   TINT160[0] */
                                 _UDWORD TINT160_1:1;  /*   TINT160[1] */
                                 _UDWORD TINT161_0:1;  /*   TINT161[0] */
                                 _UDWORD TINT161_1:1;  /*   TINT161[1] */
                                 _UDWORD TINT162_0:1;  /*   TINT162[0] */
                                 _UDWORD TINT162_1:1;  /*   TINT162[1] */
                                 _UDWORD :26;          /*              */
                                 } BIT;                /*              */
                          } ICDICFR36;                 /*              */
                    } n;                               /*              */
             } ICDICFR;                                /*              */
       _UBYTE wk19[108];                               /*              */
       union {                                         /* ppi_status   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD :11;                       /*              */
                    _UDWORD ppi_status0:1;             /*   ppi_status[0] */
                    _UDWORD ppi_status1:1;             /*   ppi_status[1] */
                    _UDWORD ppi_status2:1;             /*   ppi_status[2] */
                    _UDWORD ppi_status3:1;             /*   ppi_status[3] */
                    _UDWORD ppi_status4:1;             /*   ppi_status[4] */
                    _UDWORD :16;                       /*              */
                    } BIT;                             /*              */
             } ppi_status;                             /*              */
       union {                                         /* spi_status   */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD spi_status0:1;             /*   spi_status[0] */
                    _UDWORD spi_status1:1;             /*   spi_status[1] */
                    _UDWORD spi_status2:1;             /*   spi_status[2] */
                    _UDWORD spi_status3:1;             /*   spi_status[3] */
                    _UDWORD spi_status4:1;             /*   spi_status[4] */
                    _UDWORD spi_status5:1;             /*   spi_status[5] */
                    _UDWORD spi_status6:1;             /*   spi_status[6] */
                    _UDWORD spi_status7:1;             /*   spi_status[7] */
                    _UDWORD spi_status8:1;             /*   spi_status[8] */
                    _UDWORD spi_status9:1;             /*   spi_status[9] */
                    _UDWORD spi_status10:1;            /*   spi_status[10] */
                    _UDWORD spi_status11:1;            /*   spi_status[11] */
                    _UDWORD spi_status12:1;            /*   spi_status[12] */
                    _UDWORD spi_status13:1;            /*   spi_status[13] */
                    _UDWORD spi_status14:1;            /*   spi_status[14] */
                    _UDWORD spi_status15:1;            /*   spi_status[15] */
                    _UDWORD spi_status16:1;            /*   spi_status[16] */
                    _UDWORD spi_status17:1;            /*   spi_status[17] */
                    _UDWORD spi_status18:1;            /*   spi_status[18] */
                    _UDWORD spi_status19:1;            /*   spi_status[19] */
                    _UDWORD spi_status20:1;            /*   spi_status[20] */
                    _UDWORD spi_status21:1;            /*   spi_status[21] */
                    _UDWORD spi_status22:1;            /*   spi_status[22] */
                    _UDWORD spi_status23:1;            /*   spi_status[23] */
                    _UDWORD spi_status24:1;            /*   spi_status[24] */
                    _UDWORD spi_status25:1;            /*   spi_status[25] */
                    _UDWORD spi_status26:1;            /*   spi_status[26] */
                    _UDWORD spi_status27:1;            /*   spi_status[27] */
                    _UDWORD spi_status28:1;            /*   spi_status[28] */
                    _UDWORD spi_status29:1;            /*   spi_status[29] */
                    _UDWORD spi_status30:1;            /*   spi_status[30] */
                    _UDWORD spi_status31:1;            /*   spi_status[31] */
                    } BIT;                             /*              */
             } spi_status[17];                         /*              */
       _UBYTE wk20[440];                               /*              */
       union {                                         /* ICDSGIR      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD SGIINTID:4;                /*   SGIINTID   */
                    _UDWORD :11;                       /*              */
                    _UDWORD SATT:1;                    /*   SATT       */
                    _UDWORD CPUTargetList:8;           /*   CPUTargetList */
                    _UDWORD TargetListFilter:2;        /*   TargetListFilter */
                    _UDWORD :6;                        /*              */
                    } BIT;                             /*              */
             } ICDSGIR;                                /*              */
       _UBYTE wk21[252];                               /*              */
       union {                                         /* ICCICR       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD EnableS:1;                 /*   EnableS    */
                    _UDWORD EnableNS:1;                /*   EnableNS   */
                    _UDWORD AckCtl:1;                  /*   AckCtl     */
                    _UDWORD FIQEn:1;                   /*   FIQEn      */
                    _UDWORD SBPR:1;                    /*   SBPR       */
                    _UDWORD :27;                       /*              */
                    } BIT;                             /*              */
             } ICCICR;                                 /*              */
       union {                                         /* ICCPMR       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD Priority:8;                /*   Priority   */
                    _UDWORD :24;                       /*              */
                    } BIT;                             /*              */
             } ICCPMR;                                 /*              */
       union {                                         /* ICCBPR       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD Binarypoint:3;             /*   Binarypoint */
                    _UDWORD :29;                       /*              */
                    } BIT;                             /*              */
             } ICCBPR;                                 /*              */
       union {                                         /* ICCIAR       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD ACKINTID:10;               /*   ACKINTID   */
                    _UDWORD CPUID:3;                   /*   CPUID      */
                    _UDWORD :19;                       /*              */
                    } BIT;                             /*              */
             } ICCIAR;                                 /*              */
       union {                                         /* ICCEOIR      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD EOIINTID:10;               /*   EOIINTID   */
                    _UDWORD CPUID:3;                   /*   CPUID      */
                    _UDWORD :19;                       /*              */
                    } BIT;                             /*              */
             } ICCEOIR;                                /*              */
       union {                                         /* ICCRPR       */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD Priority:8;                /*   Priority   */
                    _UDWORD :24;                       /*              */
                    } BIT;                             /*              */
             } ICCRPR;                                 /*              */
       union {                                         /* ICCHPIR      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD PENDINTID:10;              /*   PENDINTID  */
                    _UDWORD CPUID:3;                   /*   CPUID      */
                    _UDWORD :19;                       /*              */
                    } BIT;                             /*              */
             } ICCHPIR;                                /*              */
       union {                                         /* ICCABPR      */
             _UDWORD LONG;                             /*  Long Access */
             struct {                                  /*  Bit Access  */
                    _UDWORD Binarypoint:3;             /*   Binarypoint */
                    _UDWORD :29;                       /*              */
                    } BIT;                             /*              */
             } ICCABPR;                                /*              */
       _UBYTE wk22[220];                               /*              */
       _UDWORD ICCIDR;                                 /* ICCIDR       */
};                                                     /*              */
struct st_intc_2 {                                     /* struct INTC2 */
       union {                                         /* ICR0         */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD :1;                         /*              */
                    _UWORD NMIF:1;                     /*   NMIF       */
                    _UWORD :6;                         /*              */
                    _UWORD NMIE:1;                     /*   NMIE       */
                    _UWORD :6;                         /*              */
                    _UWORD NMIL:1;                     /*   NMIL       */
                    } BIT;                             /*              */
             } ICR0;                                   /*              */
       union {                                         /* ICR1         */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD IRQ00S:1;                   /*   IRQ00S     */
                    _UWORD IRQ01S:1;                   /*   IRQ01S     */
                    _UWORD IRQ10S:1;                   /*   IRQ10S     */
                    _UWORD IRQ11S:1;                   /*   IRQ11S     */
                    _UWORD IRQ20S:1;                   /*   IRQ20S     */
                    _UWORD IRQ21S:1;                   /*   IRQ21S     */
                    _UWORD IRQ30S:1;                   /*   IRQ30S     */
                    _UWORD IRQ31S:1;                   /*   IRQ31S     */
                    _UWORD IRQ40S:1;                   /*   IRQ40S     */
                    _UWORD IRQ41S:1;                   /*   IRQ41S     */
                    _UWORD IRQ50S:1;                   /*   IRQ50S     */
                    _UWORD IRQ51S:1;                   /*   IRQ51S     */
                    _UWORD IRQ60S:1;                   /*   IRQ60S     */
                    _UWORD IRQ61S:1;                   /*   IRQ61S     */
                    _UWORD IRQ70S:1;                   /*   IRQ70S     */
                    _UWORD IRQ71S:1;                   /*   IRQ71S     */
                    } BIT;                             /*              */
             } ICR1;                                   /*              */
       _UBYTE wk0[2];                                  /*              */
       union {                                         /* IRQRR        */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD IRQ0F:1;                    /*   IRQ0F      */
                    _UWORD IRQ1F:1;                    /*   IRQ1F      */
                    _UWORD IRQ2F:1;                    /*   IRQ2F      */
                    _UWORD IRQ3F:1;                    /*   IRQ3F      */
                    _UWORD IRQ4F:1;                    /*   IRQ4F      */
                    _UWORD IRQ5F:1;                    /*   IRQ5F      */
                    _UWORD IRQ6F:1;                    /*   IRQ6F      */
                    _UWORD IRQ7F:1;                    /*   IRQ7F      */
                    _UWORD :8;                         /*              */
                    } BIT;                             /*              */
             } IRQRR;                                  /*              */
       _UBYTE wk1[16];                                 /*              */
       union {                                         /* MXIR0        */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD MXI:1;                      /*   MXI        */
                    _UWORD :15;                        /*              */
                    } BIT;                             /*              */
             } MXIR0;                                  /*              */
       union {                                         /* MXIR1        */
             _UWORD WORD;                              /*  Word Access */
             struct {                                  /*  Bit Access  */
                    _UWORD MXI:1;                      /*   MXI        */
                    _UWORD :15;                        /*              */
                    } BIT;                             /*              */
             } MXIR1;                                  /*              */
};                                                     /*              */

#ifndef ARM_SIM
#define INTC  (*(volatile struct st_intc *)  0xE8201000)  /* INTC  Address */
#define INTC2 (*(volatile struct st_intc_2 *)0xFCFEF800)  /* INTC2 Address */
#else	/* ARM_SIM */
#define INTC  (*(volatile struct st_intc *)  0x45201000)  /* INTC  Address */
#define INTC2 (*(volatile struct st_intc_2 *)0x49FEF800)  /* INTC2 Address */
#endif	/* ARM_SIM */

#endif /* __INTC_IODEFINE_H__ */

/* End of File */
