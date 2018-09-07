/******************************************************************************
*   DISCLAIMER
*
*   This software is supplied by Renesas Technology Corp. and is only 
*   intended for use with Renesas products. No other uses are authorized.
*
*   This software is owned by Renesas Technology Corp. and is protected under 
*   all applicable laws, including copyright laws.
*
*   THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES 
*   REGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, 
*   INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A 
*   PARTICULAR PURPOSE AND NON-INFRINGEMENT.  ALL SUCH WARRANTIES ARE EXPRESSLY 
*   DISCLAIMED.
*
*   TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS 
*   TECHNOLOGY CORP. NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE 
*   FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES 
*   FOR ANY REASON RELATED TO THE THIS SOFTWARE, EVEN IF RENESAS OR ITS 
*   AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
*
*   Renesas reserves the right, without notice, to make changes to this 
*   software and to discontinue the availability of this software.
*   By using this software, you agree to the additional terms and 
*   conditions found by accessing the following link: 
*   http://www.renesas.com/disclaimer
********************************************************************************
*   Copyright (C) 2009. Renesas Technology Corp., All Rights Reserved.
*""FILE COMMENT""*********** Technical reference data **************************
*   System Name : SH7216 Sample Program
*   File Name   : iodefine.h
*   Abstract    : SH7216 IO register definition
*   Version     : 0.05.00
*   Device      : SH7216
*   Tool-Chain  : High-performance Embedded Workshop (Ver.4.05.01).
*               : C/C++ compiler package for the SuperH RISC engine family
*               :                             (Ver.9.03 Release00).
*   OS          : None
*   H/W Platform: R0K572167 (CPU board)
*   Description : 
********************************************************************************
*   History     : Mar.10,2009 Ver.0.05.00  
*""FILE COMMENT END""**********************************************************/
#ifndef _IODEFINE_H_
#define _IODEFINE_H_

struct st_cpg {                                             /* struct CPG   */
        union {                                             /* FRQCR        *///FFFE0010
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short              : 5;            /*              */
                unsigned short STC          : 3;            /*    STC       */
                unsigned short              : 1;            /*              */
                unsigned short IFC          : 3;            /*    IFC       */
                unsigned short              : 1;            /*              */
                unsigned short _PFC         : 3;            /*    PFC       */
            }           BIT;                                /*              */
        }               FRQCR;                              /*              */
        char            wk1[10];                            /*              *///FFFE001C-FFFE0010-2
        union {                                             /* OSCCR        *///FFFE001C
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char OSCSTOP       : 1;            /*    OSCSTOP   */
                unsigned char               : 1;            /*              */
                unsigned char OSCERS        : 1;            /*    OSCERS    */
            }           BIT;                                /*              */
        }               OSCCR;                              /*              */
        char            wk2[1011];                          /*              *///FFFE0410-FFFE001C-1
        union {                                             /* MCLKCR       *///FFFE0410
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char               : 4;            /*              */
                unsigned char MSDIVS        : 2;            /*    MSDIVS    */
            }           BIT;                                /*              */
        }               MCLKCR;                             /*              */
        char            wk3[3];                             /*              *///FFFE0414-FFFE0410-1
        union {                                             /* ACLKCR       *///FFFE0414
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char               : 4;            /*              */
                unsigned char ASDIVS        : 2;            /*    ASDIVS    */
            }           BIT;                                /*              */
        }               ACLKCR;                             /*              */
};                                                          /*              */
struct st_intc {                                            /* struct INTC  */
        union {                                             /* ICR0         *///FFFE0800
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short NMIL         : 1;            /*    NMIL      */
                unsigned short              : 6;            /*              */
                unsigned short NMIE         : 1;            /*    NMIE      */
            }           BIT;                                /*              */
        }               ICR0;                               /*              */
        union {                                             /* ICR1         *///FFFE0802
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short IRQ7S        : 2;            /*    IRQ7S     */
                unsigned short IRQ6S        : 2;            /*    IRQ6S     */
                unsigned short IRQ5S        : 2;            /*    IRQ5S     */
                unsigned short IRQ4S        : 2;            /*    IRQ4S     */
                unsigned short IRQ3S        : 2;            /*    IRQ3S     */
                unsigned short IRQ2S        : 2;            /*    IRQ2S     */
                unsigned short IRQ1S        : 2;            /*    IRQ1S     */
                unsigned short IRQ0S        : 2;            /*    IRQ0S     */
            }           BIT;                                /*              */
        }               ICR1;                               /*              */
        char            wk1[2];                             /*              *///FFFE0806-FFFE0802-2
        union {                                             /* IRQRR        *///FFFE0806
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short              : 8;            /*              */
                unsigned short IRQ7F        : 1;            /*    IRQ7F     */
                unsigned short IRQ6F        : 1;            /*    IRQ6F     */
                unsigned short IRQ5F        : 1;            /*    IRQ5F     */
                unsigned short IRQ4F        : 1;            /*    IRQ4F     */
                unsigned short IRQ3F        : 1;            /*    IRQ3F     */
                unsigned short IRQ2F        : 1;            /*    IRQ2F     */
                unsigned short IRQ1F        : 1;            /*    IRQ1F     */
                unsigned short IRQ0F        : 1;            /*    IRQ0F     */
            }           BIT;                                /*              */
        }               IRQRR;                              /*              */
        char            wk2[4];                             /*              *///FFFE080C-FFFE0806-2
        union {                                             /* IBCR         *///FFFE080C
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short E15          : 1;            /*    E15       */
                unsigned short E14          : 1;            /*    E14       */
                unsigned short E13          : 1;            /*    E13       */
                unsigned short E12          : 1;            /*    E12       */
                unsigned short E11          : 1;            /*    E11       */
                unsigned short E10          : 1;            /*    E10       */
                unsigned short E9           : 1;            /*    E9        */
                unsigned short E8           : 1;            /*    E8        */
                unsigned short E7           : 1;            /*    E7        */
                unsigned short E6           : 1;            /*    E6        */
                unsigned short E5           : 1;            /*    E5        */
                unsigned short E4           : 1;            /*    E4        */
                unsigned short E3           : 1;            /*    E3        */
                unsigned short E2           : 1;            /*    E2        */
                unsigned short E1           : 1;            /*    E1        */
            }           BIT;                                /*              */
        }               IBCR;                               /*              */
        union {                                             /* IBNR         *///FFFE080E
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short BE           : 2;            /*    BE        */
                unsigned short BOVE         : 1;            /*    BOVE      */
                unsigned short              : 9;            /*              */
                unsigned short BN           : 4;            /*    BN        */
            }           BIT;                                /*              */
        }               IBNR;                               /*              */
        char            wk3[8];                             /*              *///FFFE0818-FFFE080C-4
        union {                                             /* IPR01        *///FFFE0818
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short _IRQ0        : 4;            /*    IRQ0      */
                unsigned short _IRQ1        : 4;            /*    IRQ1      */
                unsigned short _IRQ2        : 4;            /*    IRQ2      */
                unsigned short _IRQ3        : 4;            /*    IRQ3      */
            }           BIT;                                /*              */
        }               IPR01;                              /*              */
        union {                                             /* IPR02        *///FFFE081A
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short _IRQ4        : 4;            /*    IRQ4      */
                unsigned short _IRQ5        : 4;            /*    IRQ5      */
                unsigned short _IRQ6        : 4;            /*    IRQ6      */
                unsigned short _IRQ7        : 4;            /*    IRQ7      */
            }           BIT;                                /*              */
        }               IPR02;                              /*              */
        char            wk4[4];                             /*              *///FFFE0820-FFFE081A-2
        union {                                             /* IPR05        *///FFFE0820
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short              : 4;            /*              */
                unsigned short              : 4;            /*              */
                unsigned short _AD0         : 4;            /*    AD0       */
                unsigned short _AD1         : 4;            /*    AD1       */
            }           BIT;                                /*              */
        }               IPR05;                              /*              */
        char            wk5[990];                           /*              *///FFFE0C00-FFFE0820-2
        union {                                             /* IPR06        *///FFFE0C00
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short _DMAC0       : 4;            /*    DMAC0     */
                unsigned short _DMAC1       : 4;            /*    DMAC1     */
                unsigned short _DMAC2       : 4;            /*    DMAC2     */
                unsigned short _DMAC3       : 4;            /*    DMAC3     */
            }           BIT;                                /*              */
        }               IPR06;                              /*              */
        union {                                             /* IPR07        *///FFFE0C02
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short _DMAC4       : 4;            /*    DMAC4     */
                unsigned short _DMAC5       : 4;            /*    DMAC5     */
                unsigned short _DMAC6       : 4;            /*    DMAC6     */
                unsigned short _DMAC7       : 4;            /*    DMAC7     */
            }           BIT;                                /*              */
        }               IPR07;                              /*              */
        union {                                             /* IPR08        *///FFFE0C04
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short _CMT0        : 4;            /*    CMT0      */
                unsigned short _CMT1        : 4;            /*    CMT1      */
                unsigned short _BSC         : 4;            /*    BSC       */
                unsigned short _WDT         : 4;            /*    WDT       */
            }           BIT;                                /*              */
        }               IPR08;                              /*              */
        union {                                             /* IPR09        *///FFFE0C06
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short _MTU20G      : 4;            /*    MTU20 TGI */
                unsigned short _MTU20C      : 4;            /*    MTU20 TCI */
                unsigned short _MTU21G      : 4;            /*    MTU21 TGI */
                unsigned short _MTU21C      : 4;            /*    MTU21 TCI */
            }           BIT;                                /*              */
        }               IPR09;                              /*              */
        union {                                             /* IPR10        *///FFFE0C08
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short _MTU22G      : 4;            /*    MTU22 TGI */
                unsigned short _MTU22C      : 4;            /*    MTU22 TCI */
                unsigned short _MTU23G      : 4;            /*    MTU23 TGI */
                unsigned short _MTU23C      : 4;            /*    MTU23 TCI */
            }           BIT;                                /*              */
        }               IPR10;                              /*              */
        union {                                             /* IPR11        *///FFFE0C0A
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short _MTU24G      : 4;            /*    MTU24 TGI */
                unsigned short _MTU24C      : 4;            /*    MTU24 TCI */
                unsigned short _MTU25       : 4;            /*    MTU25     */
                unsigned short _POE2        : 4;            /*    POE2      */
            }           BIT;                                /*              */
        }               IPR11;                              /*              */
        union {                                             /* IPR12        *///FFFE0C0C
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short _MTU2S3G     : 4;            /*    MTU2S3 TGI*/
                unsigned short _MTU2S3C     : 4;            /*    MTU2S3 TCI*/
                unsigned short _MTU2S4G     : 4;            /*    MTU2S4 TGI*/
                unsigned short _MTU2S4C     : 4;            /*    MTU2S4 TCI*/
            }           BIT;                                /*              */
        }               IPR12;                              /*              */
        union {                                             /* IPR13        *///FFFE0C0E
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short _MTU2S5      : 4;            /*    MTU2S5    */
                unsigned short _POE2        : 4;            /*    POE2      */
                unsigned short _IIC3        : 4;            /*    IIC3      */
            }           BIT;                                /*              */
        }               IPR13;                              /*              */
        union {                                             /* IPR14        *///FFFE0C10
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short              : 4;            /*              */
                unsigned short              : 4;            /*              */
                unsigned short              : 4;            /*              */
                unsigned short _SCIF3       : 4;            /*    SCIF3     */
            }           BIT;                                /*              */
        }               IPR14;                              /*              */
        union {                                             /* IPR15        *///FFFE0C12
            unsigned short WORD;                            /*  Word Access */
        }               IPR15;                              /*              */
        union {                                             /* IPR16        *///FFFE0C14
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short _SCI0        : 4;            /*    SCI0      */
                unsigned short _SCI1        : 4;            /*    SCI1      */
                unsigned short _SCI2        : 4;            /*    SCI2      */
            }           BIT;                                /*              */
        }               IPR16;                              /*              */
        union {                                             /* IPR17        *///FFFE0C16
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short _RSPI        : 4;            /*    RSPI      */
                unsigned short _SCI4        : 4;            /*    SCI4      */
            }           BIT;                                /*              */
        }               IPR17;                              /*              */
        union {                                             /* IPR18        *///FFFE0C18
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short _USB         : 4;            /*    USB       */
                unsigned short _RCAN        : 4;            /*    RCAN      */
                unsigned short _EP1FULL     : 4;            /*    EP1FULL   */
                unsigned short _EP2EMPTY    : 4;            /*    EP2EMPTY  */
            }           BIT;                                /*              */
        }               IPR18;                              /*              */
        union {                                             /* IPR19        *///FFFE0C1A
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short _EP4FULL     : 4;            /*    EP4FULL   */
                unsigned short _EP5EMPTY    : 4;            /*    EP5EMPTY  */
                unsigned short _EDMAC       : 4;            /*    E-DMAC    */
            }           BIT;                                /*              */
        }               IPR19;                              /*              */
        char            wk6[52];                            /*              *///FFFE0C50-FFFE0C1A-2
        union {                                             /* USDTENDRR    *///FFFE0C50
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short _RXF0        : 1;            /*    RXF0      */
                unsigned short _TXF0        : 1;            /*    TXF0      */
                unsigned short _RXF1        : 1;            /*    RXF1      */
                unsigned short _TXF1        : 1;            /*    TXF1      */
            }           BIT;                                /*              */
        }               USDTENDRR;                          /*              */
};                                                          /*              */
struct st_ubc {                                             /* struct UBC   */
        union {                                             /* BRCR         *///FFFC04C0
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :14;            /*              */
                unsigned int CKS            : 2;            /*    CKS       */
                unsigned int SCMFC0         : 1;            /*    SCMFC0    */
                unsigned int SCMFC1         : 1;            /*    SCMFC1    */
                unsigned int SCMFC2         : 1;            /*    SCMFC2    */
                unsigned int SCMFC3         : 1;            /*    SCMFC3    */
                unsigned int SCMFD0         : 1;            /*    SCMFD0    */
                unsigned int SCMFD1         : 1;            /*    SCMFD1    */
                unsigned int SCMFD2         : 1;            /*    SCMFD2    */
                unsigned int SCMFD3         : 1;            /*    SCMFD3    */
                unsigned int PCB3           : 1;            /*    PCB3      */
                unsigned int PCB2           : 1;            /*    PCB2      */
                unsigned int PCB1           : 1;            /*    PCB1      */
                unsigned int PCB0           : 1;            /*    PCB0      */
            }           BIT;                                /*              */
        }               BRCR;                               /*              */
};                                                          /*              */
struct st_ubc0 {                                            /* struct UBC0/1*///FFFC0400/FFFC0410
        void            *BAR;                               /* BAR          */
        unsigned int    BAMR;                               /* BAMR         */
        char            wk1[152];                           /*              *///FFFC04A0-FFFC0400-8
        union {                                             /* BBR          *///FFFC04A0
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short              : 2;            /*              */
                unsigned short UBID         : 1;            /*    UBID      */
                unsigned short              : 2;            /*              */
                unsigned short CP           : 3;            /*    CP        */
                unsigned short CD           : 2;            /*    CD        */
                unsigned short ID           : 2;            /*    ID        */
                unsigned short RW           : 2;            /*    RW        */
                unsigned short SZ           : 2;            /*    SZ        */
            }           BIT;                                /*              */
        }               BBR;                                /*              */
};                                                          /*              */
struct st_ubc2 {                                            /* struct UBC2/3*///FFFC0420/FFFC0430
        void            *BAR;                               /* BAR          */
        unsigned int    BAMR;                               /* BAMR         */
        char            wk1[124];                           /*              *///FFFC04A4-FFFC0424-4
        union {                                             /* BBR          *///FFFC04A4
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short              : 2;            /*              */
                unsigned short UBID         : 1;            /*    UBID      */
                unsigned short              : 2;            /*              */
                unsigned short CP           : 3;            /*    CP        */
                unsigned short CD           : 2;            /*    CD        */
                unsigned short ID           : 2;            /*    ID        */
                unsigned short RW           : 2;            /*    RW        */
                unsigned short SZ           : 2;            /*    SZ        */
            }           BIT;                                /*              */
        }               BBR;                                /*              */
};                                                          /*              */
struct st_dtc {                                             /* struct DTC   */
        union {                                             /* DTCERA       *///FFFE6000
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned char IRQ0          : 1;            /*    IRQ0      */
                unsigned char IRQ1          : 1;            /*    IRQ1      */
                unsigned char IRQ2          : 1;            /*    IRQ2      */
                unsigned char IRQ3          : 1;            /*    IRQ3      */
                unsigned char IRQ4          : 1;            /*    IRQ4      */
                unsigned char IRQ5          : 1;            /*    IRQ5      */
                unsigned char IRQ6          : 1;            /*    IRQ6      */
                unsigned char IRQ7          : 1;            /*    IRQ7      */
                unsigned char ADI0          : 1;            /*    ADI0      */
                unsigned char ADI1          : 1;            /*    ADI1      */
                unsigned char               : 1;            /*              */
                unsigned char RM0           : 1;            /*    RM0(RCAN) */
                unsigned char CMI0          : 1;            /*    CMI0      */
                unsigned char CMI1          : 1;            /*    CMI1      */
                unsigned char USBRXI0       : 1;            /*    USBRXI0   *///USB EP1FULL
                unsigned char USBTXI0       : 1;            /*    USBTXI0   *///USB EP2EMPTY
            }           BIT;                                /*              */
        }               DTCERA;                             /*              */
        union {                                             /* DTCERB       *///FFFE6002
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned char TGIA0         : 1;            /*    TGIA0     *///MTU2
                unsigned char TGIB0         : 1;            /*    TGIB0     */
                unsigned char TGIC0         : 1;            /*    TGIC0     */
                unsigned char TGID0         : 1;            /*    TGID0     */
                unsigned char TGIA1         : 1;            /*    TGIA1     */
                unsigned char TGIB1         : 1;            /*    TGIB1     */
                unsigned char TGIA2         : 1;            /*    TGIA2     */
                unsigned char TGIB2         : 1;            /*    TGIB2     */
                unsigned char TGIA3         : 1;            /*    TGIA3     */
                unsigned char TGIB3         : 1;            /*    TGIB3     */
                unsigned char TGIC3         : 1;            /*    TGIC3     */
                unsigned char TGID3         : 1;            /*    TGID3     */
                unsigned char TGIA4         : 1;            /*    TGIA4     */
                unsigned char TGIB4         : 1;            /*    TGIB4     */
                unsigned char TGIC4         : 1;            /*    TGIC4     */
                unsigned char TGID4         : 1;            /*    TGID4     */
            }           BIT;                                /*              */
        }               DTCERB;                             /*              */
        union {                                             /* DTCERC       *///FFFE6004
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned char TCIV4         : 1;            /*    TCIV4     */
                unsigned char TGIU5         : 1;            /*    TGIU5     */
                unsigned char TGIV5         : 1;            /*    TGIV5     */
                unsigned char TGIW5         : 1;            /*    TGIW5     *///MTU2
                unsigned char               : 4;            /*              */
                unsigned char               : 4;            /*              */
                unsigned char TGIA3S        : 1;            /*    TGIA3S    *///MTU2S
                unsigned char TGIB3S        : 1;            /*    TGIB3S    */
                unsigned char TGIC3S        : 1;            /*    TGIC3S    */
                unsigned char TGID3S        : 1;            /*    TGID3S    */
            }           BIT;                                /*              */
        }               DTCERC;                             /*              */
        union {                                             /* DTCERD       *///FFFE6006
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned char TGIA4S        : 1;            /*    TGIA4S    */
                unsigned char TGIB4S        : 1;            /*    TGIB4S    */
                unsigned char TGIC4S        : 1;            /*    TGIC4S    */
                unsigned char TGID4S        : 1;            /*    TGID4S    */
                unsigned char TCIV4S        : 1;            /*    TCIV4S    */
                unsigned char TGIU5S        : 1;            /*    TGIU5S    */
                unsigned char TGIV5S        : 1;            /*    TGIV5S    */
                unsigned char TGIW5S        : 1;            /*    TGIW5S    *///MTU2S
                unsigned char RXI           : 1;            /*    RXI       *///IIC3
                unsigned char TXI           : 1;            /*    TXI       *///IIC3
                unsigned char SPRXI         : 1;            /*    SPRXI     *///RSPI
                unsigned char SPTXI         : 1;            /*    SPTXI     *///RSPI
                unsigned char RXI4          : 1;            /*    RXI4      *///SCI4
                unsigned char TXI4          : 1;            /*    TXI4      *///SCI4
            }           BIT;                                /*              */
        }               DTCERD;                             /*              */
        union {                                             /* DTCERE       *///FFFE6008
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned char RXI0          : 1;            /*    RXI0      *///SCI0
                unsigned char TXI0          : 1;            /*    TXI0      *///SCI0
                unsigned char RXI1          : 1;            /*    RXI1      *///SCI1
                unsigned char TXI1          : 1;            /*    TXI1      *///SCI1
                unsigned char RXI2          : 1;            /*    RXI2      *///SCI2
                unsigned char TXI2          : 1;            /*    TXI2      *///SCI2
                unsigned char RXI3          : 1;            /*    RXIF3     *///SCIF3
                unsigned char TXI3          : 1;            /*    TXIF3     *///SCIF3
                unsigned char USBRXI1       : 1;            /*    USBRXI1   *///USB EP4FULL
                unsigned char USBTXI1       : 1;            /*    USBTXI1   *///USB EP5EMPTY
            }           BIT;                                /*              */
        }               DTCERE;                             /*              */
        char            wk1[6];                             /*              *///FFFE6010-FFFE6008-2
        union {                                             /* DTCCR        *///FFFE6010
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 3;            /*              */
                unsigned char RRS           : 1;            /*    RRS       */
                unsigned char RCHNE         : 1;            /*    RCHNE     */
                unsigned char               : 2;            /*              */
                unsigned char ERR           : 1;            /*    ERR       */
            }           BIT;                                /*              */
        }               DTCCR;                              /*              */
        char            wk2[3];                             /*              *///FFFE6014-FFFE6010-1
        unsigned int    DTCVBR;                             /* DTCVBR       *///FFFE6014
};                                                          /*              */
struct st_bsc {                                             /* struct BSC   */
        union {                                             /* CMNCR        *///FFFC0000
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :20;            /*              */
                unsigned int BLOCK          : 1;            /*    BLOCK     */
                unsigned int DPRTY          : 2;            /*    DPRTY     */
                unsigned int DMAIW          : 3;            /*    DMAIW     */
                unsigned int DMAIWA         : 1;            /*    DMAIWA    */
                unsigned int                : 2;            /*              */
                unsigned int HIZCKIO        : 1;            /*    HIZCKIO   */
                unsigned int HIZMEM         : 1;            /*    HIZMEM    */
                unsigned int HIZCNT         : 1;            /*    HIZCNT    */
            }           BIT;                                /*              */
        }               CMNCR;                              /*              */
        union {                                             /* CS0BCR       *///FFFC0004
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                : 1;            /*              */
                unsigned int IWW            : 3;            /*    IWW       */
                unsigned int IWRWD          : 3;            /*    IWRWD     */
                unsigned int IWRWS          : 3;            /*    IWRWS     */
                unsigned int IWRRD          : 3;            /*    IWRRD     */
                unsigned int IWRRS          : 3;            /*    IWRRS     */
                unsigned int                : 1;            /*              */
                unsigned int TYPE           : 3;            /*    TYPE      */
                unsigned int ENDIAN         : 1;            /*    ENDIAN    */
                unsigned int BSZ            : 2;            /*    BSZ       */
            }           BIT;                                /*              */
        }               CS0BCR;                             /*              */
        union {                                             /* CS1BCR       *///FFFC0008
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                : 1;            /*              */
                unsigned int IWW            : 3;            /*    IWW       */
                unsigned int IWRWD          : 3;            /*    IWRWD     */
                unsigned int IWRWS          : 3;            /*    IWRWS     */
                unsigned int IWRRD          : 3;            /*    IWRRD     */
                unsigned int IWRRS          : 3;            /*    IWRRS     */
                unsigned int                : 1;            /*              */
                unsigned int TYPE           : 3;            /*    TYPE      */
                unsigned int ENDIAN         : 1;            /*    ENDIAN    */
                unsigned int BSZ            : 2;            /*    BSZ       */
            }           BIT;                                /*              */
        }               CS1BCR;                             /*              */
        union {                                             /* CS2BCR       *///FFFC000C
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                : 1;            /*              */
                unsigned int IWW            : 3;            /*    IWW       */
                unsigned int IWRWD          : 3;            /*    IWRWD     */
                unsigned int IWRWS          : 3;            /*    IWRWS     */
                unsigned int IWRRD          : 3;            /*    IWRRD     */
                unsigned int IWRRS          : 3;            /*    IWRRS     */
                unsigned int                : 1;            /*              */
                unsigned int TYPE           : 3;            /*    TYPE      */
                unsigned int ENDIAN         : 1;            /*    ENDIAN    */
                unsigned int BSZ            : 2;            /*    BSZ       */
            }           BIT;                                /*              */
        }               CS2BCR;                             /*              */
        union {                                             /* CS3BCR       *///FFFC0010
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                : 1;            /*              */
                unsigned int IWW            : 3;            /*    IWW       */
                unsigned int IWRWD          : 3;            /*    IWRWD     */
                unsigned int IWRWS          : 3;            /*    IWRWS     */
                unsigned int IWRRD          : 3;            /*    IWRRD     */
                unsigned int IWRRS          : 3;            /*    IWRRS     */
                unsigned int                : 1;            /*              */
                unsigned int TYPE           : 3;            /*    TYPE      */
                unsigned int ENDIAN         : 1;            /*    ENDIAN    */
                unsigned int BSZ            : 2;            /*    BSZ       */
            }           BIT;                                /*              */
        }               CS3BCR;                             /*              */
        union {                                             /* CS4BCR       *///FFFC0014
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                : 1;            /*              */
                unsigned int IWW            : 3;            /*    IWW       */
                unsigned int IWRWD          : 3;            /*    IWRWD     */
                unsigned int IWRWS          : 3;            /*    IWRWS     */
                unsigned int IWRRD          : 3;            /*    IWRRD     */
                unsigned int IWRRS          : 3;            /*    IWRRS     */
                unsigned int                : 1;            /*              */
                unsigned int TYPE           : 3;            /*    TYPE      */
                unsigned int ENDIAN         : 1;            /*    ENDIAN    */
                unsigned int BSZ            : 2;            /*    BSZ       */
            }           BIT;                                /*              */
        }               CS4BCR;                             /*              */
        union {                                             /* CS5BCR       *///FFFC0018
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                : 1;            /*              */
                unsigned int IWW            : 3;            /*    IWW       */
                unsigned int IWRWD          : 3;            /*    IWRWD     */
                unsigned int IWRWS          : 3;            /*    IWRWS     */
                unsigned int IWRRD          : 3;            /*    IWRRD     */
                unsigned int IWRRS          : 3;            /*    IWRRS     */
                unsigned int                : 1;            /*              */
                unsigned int TYPE           : 3;            /*    TYPE      */
                unsigned int ENDIAN         : 1;            /*    ENDIAN    */
                unsigned int BSZ            : 2;            /*    BSZ       */
            }           BIT;                                /*              */
        }               CS5BCR;                             /*              */
        union {                                             /* CS6BCR       *///FFFC001C
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                : 1;            /*              */
                unsigned int IWW            : 3;            /*    IWW       */
                unsigned int IWRWD          : 3;            /*    IWRWD     */
                unsigned int IWRWS          : 3;            /*    IWRWS     */
                unsigned int IWRRD          : 3;            /*    IWRRD     */
                unsigned int IWRRS          : 3;            /*    IWRRS     */
                unsigned int                : 1;            /*              */
                unsigned int TYPE           : 3;            /*    TYPE      */
                unsigned int ENDIAN         : 1;            /*    ENDIAN    */
                unsigned int BSZ            : 2;            /*    BSZ       */
            }           BIT;                                /*              */
        }               CS6BCR;                             /*              */
        union {                                             /* CS7BCR       *///FFFC0020
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                : 1;            /*              */
                unsigned int IWW            : 3;            /*    IWW       */
                unsigned int IWRWD          : 3;            /*    IWRWD     */
                unsigned int IWRWS          : 3;            /*    IWRWS     */
                unsigned int IWRRD          : 3;            /*    IWRRD     */
                unsigned int IWRRS          : 3;            /*    IWRRS     */
                unsigned int                : 1;            /*              */
                unsigned int TYPE           : 3;            /*    TYPE      */
                unsigned int ENDIAN         : 1;            /*    ENDIAN    */
                unsigned int BSZ            : 2;            /*    BSZ       */
            }           BIT;                                /*              */
        }               CS7BCR;                             /*              */
        char            wk1[4];                             /*              *///FFFC0028-FFFC0020-4
        unsigned int    CS0WCR;                             /* CS0WCR       *///FFFC0028
        unsigned int    CS1WCR;                             /* CS1WCR       *///FFFC002C
        unsigned int    CS2WCR;                             /* CS2WCR       *///FFFC0030
        unsigned int    CS3WCR;                             /* CS3WCR       *///FFFC0034
        unsigned int    CS4WCR;                             /* CS4WCR       *///FFFC0038
        unsigned int    CS5WCR;                             /* CS5WCR       *///FFFC003C
        unsigned int    CS6WCR;                             /* CS6WCR       *///FFFC0040
        unsigned int    CS7WCR;                             /* CS7WCR       *///FFFC0044
        char            wk2[4];                             /*              *///FFFC004C-FFFC0044-4
        union {                                             /* SDCR         *///FFFC004C
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :11;            /*              */
                unsigned int A2ROW          : 2;            /*    A2ROW     */
                unsigned int                : 1;            /*              */
                unsigned int A2COL          : 2;            /*    A2COL     */
                unsigned int                : 2;            /*              */
                unsigned int DEEP           : 1;            /*    DEEP      */
                unsigned int SLOW           : 1;            /*    SLOW      */
                unsigned int RFSH           : 1;            /*    RFSH      */
                unsigned int RMODE          : 1;            /*    RMODE     */
                unsigned int PDOWN          : 1;            /*    PDOWN     */
                unsigned int BACTV          : 1;            /*    BACTV     */
                unsigned int                : 3;            /*              */
                unsigned int A3ROW          : 2;            /*    A3ROW     */
                unsigned int                : 1;            /*              */
                unsigned int A3COL          : 2;            /*    A3COL     */
            }           BIT;                                /*              */
        }               SDCR;                               /*              */
        union {                                             /* RTCSR        *///FFFC0050
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :24;            /*              */
                unsigned int CMF            : 1;            /*    CMF       */
                unsigned int CMIE           : 1;            /*    CMIE      */
                unsigned int CKS            : 3;            /*    CKS       */
                unsigned int RRC            : 3;            /*    RRC       */
            }           BIT;                                /*              */
        }               RTCSR;                              /*              */
        unsigned int        RTCNT;                          /* RTCNT        *///FFFC0054
        unsigned int        RTCOR;                          /* RTCOR        *///FFFC0058
        char            wk3[146366];                        /*              *///FFFE3C1A-FFFC0058-4
        union {                                             /* BSCEHR       *///FFFE3C1A
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short DTLOCK       : 1;            /*    DTLOCK    */
                unsigned short              : 3;            /*              */
                unsigned short DTBST        : 1;            /*    DTBST     */
                unsigned short DTSA         : 1;            /*    DTSA      */
                unsigned short              : 1;            /*              */
                unsigned short DTPR         : 1;            /*    DTPR      */
            }           BIT;                                /*              */
        }               BSCEHR;                             /*              */
};                                                          /*              */
struct st_dmac {                                            /* struct DMAC  */
        union {                                             /* DMAOR        *///FFFE1200
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char CMS           : 2;            /*    CMS       */
                unsigned char               : 2;            /*              */
                unsigned char PR            : 2;            /*    PR        */
                unsigned char               : 5;            /*              */
                unsigned char AE            : 1;            /*    AE        */
                unsigned char NMIF          : 1;            /*    NMIF      */
                unsigned char DME           : 1;            /*    DME       */
            }           BIT;                                /*              */
        }               DMAOR;                              /*              */
        char            wk1[254];                           /*              *///FFFE1300-FFFE1200-2
        union {                                             /* DMARS0       *///FFFE1300
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short C1MID        : 6;            /*    C1MID     */
                unsigned short C1RID        : 2;            /*    C1RID     */
                unsigned short C0MID        : 6;            /*    C0MID     */
                unsigned short C0RID        : 2;            /*    C0RID     */
            }           BIT;                                /*              */
        }               DMARS0;                             /*              */
        char            wk2[2];                             /*              *///FFFE1304-FFFE1300-2
        union {                                             /* DMARS1       *///FFFE1304
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short C3MID        : 6;            /*    C3MID     */
                unsigned short C3RID        : 2;            /*    C3RID     */
                unsigned short C2MID        : 6;            /*    C2MID     */
                unsigned short C2RID        : 2;            /*    C2RID     */
            }           BIT;                                /*              */
        }               DMARS1;                             /*              */
        char            wk3[2];                             /*              *///FFFE1308-FFFE1304-2
        union {                                             /* DMARS2       *///FFFE1308
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short C5MID        : 6;            /*    C5MID     */
                unsigned short C5RID        : 2;            /*    C5RID     */
                unsigned short C4MID        : 6;            /*    C4MID     */
                unsigned short C4RID        : 2;            /*    C4RID     */
            }           BIT;                                /*              */
        }               DMARS2;                             /*              */
        char            wk4[2];                             /*              *///FFFE130C-FFFE1308-2
        union {                                             /* DMARS3       *///FFFE130C
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short C7MID        : 6;            /*    C7MID     */
                unsigned short C7RID        : 2;            /*    C7RID     */
                unsigned short C6MID        : 6;            /*    C6MID     */
                unsigned short C6RID        : 2;            /*    C6RID     */
            }           BIT;                                /*              */
        }               DMARS3;                             /*              */
};                                                          /*              */
struct st_dmac0 {                                           /* struct DMAC0 *///FFFE1000
                                                            /* struct DMAC1 *///FFFE1010
        void            *SAR;                               /* SAR          *///FFFE1000
        void            *DAR;                               /* DAR          *///FFFE1004
        unsigned int    DMATCR;                             /* DMATCR       *///FFFE1008
        union {                                             /* CHCR         *///FFFE100C
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Word Access */
                unsigned short H;                           /*    High Word */
                unsigned short L;                           /*    Low  Word */
            }       WORD;                                   /*              */
            struct {                                        /*  Bit Access  */
                unsigned char TC            : 1;            /*    TC        */
                unsigned char               : 2;            /*              */
                unsigned char RLD           : 1;            /*    RLD       */
                unsigned char               : 4;            /*              */
                unsigned char DO            : 1;            /*    DO        */
                unsigned char TL            : 1;            /*    TL        */
                unsigned char               : 2;            /*              */
                unsigned char HE            : 1;            /*    HE        */
                unsigned char HIE           : 1;            /*    HIE       */
                unsigned char AM            : 1;            /*    AM        */
                unsigned char AL            : 1;            /*    AL        */
                unsigned char DM            : 2;            /*    DM        */
                unsigned char SM            : 2;            /*    SM        */
                unsigned char RS            : 4;            /*    RS        */
                unsigned char DL            : 1;            /*    DL        */
                unsigned char DS            : 1;            /*    DS        */
                unsigned char TB            : 1;            /*    TB        */
                unsigned char TS            : 2;            /*    TS        */
                unsigned char IE            : 1;            /*    IE        */
                unsigned char TE            : 1;            /*    TE        */
                unsigned char DE            : 1;            /*    DE        */
            }           BIT;                                /*              */
        }               CHCR;                               /*              */
        char            wk1[240];                           /*              *///FFFE1100-FFFE100C-4
        void            *RSAR;                              /* RSAR         *///FFFE1100
        void            *RDAR;                              /* RDAR         *///FFFE1104
        unsigned int    RDMATCR;                            /* RDMATCR      *///FFFE1108
};                                                          /*              */
struct st_dmac2 {                                           /* struct DMAC2 *///FFFE1020
                                                            /* struct DMAC3 *///FFFE1030
        void            *SAR;                               /* SAR          *///FFFE1020
        void            *DAR;                               /* DAR          *///FFFE1024
        unsigned int    DMATCR;                             /* DMATCR       *///FFFE1028
        union {                                             /* CHCR         *///FFFE102C
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Word Access */
                unsigned short H;                           /*    High Word */
                unsigned short L;                           /*    Low  Word */
            }           WORD;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char TC            : 1;            /*    TC        */
                unsigned char               : 2;            /*              */
                unsigned char RLD           : 1;            /*    RLD       */
                unsigned char               : 4;            /*              */
                unsigned char DO            : 1;            /*    DO        */
                unsigned char               : 3;            /*              */
                unsigned char HE            : 1;            /*    HE        */
                unsigned char HIE           : 1;            /*    HIE       */
                unsigned char AM            : 1;            /*    AM        */
                unsigned char AL            : 1;            /*    AL        */
                unsigned char DM            : 2;            /*    DM        */
                unsigned char SM            : 2;            /*    SM        */
                unsigned char RS            : 4;            /*    RS        */
                unsigned char DL            : 1;            /*    DL        */
                unsigned char DS            : 1;            /*    DS        */
                unsigned char TB            : 1;            /*    TB        */
                unsigned char TS            : 2;            /*    TS        */
                unsigned char IE            : 1;            /*    IE        */
                unsigned char TE            : 1;            /*    TE        */
                unsigned char DE            : 1;            /*    DE        */
            }           BIT;                                /*              */
        }               CHCR;                               /*              */
        char            wk1[240];                           /*              *///FFFE1120-FFFE102C-4
        void            *RSAR;                              /* RSAR         *///FFFE1120
        void            *RDAR;                              /* RDAR         *///FFFE1124
        unsigned int    RDMATCR;                            /* RDMATCR      *///FFFE1128
};                                                          /*              */
struct st_dmac4 {                                           /* struct DMAC4 *///FFFE1040
                                                            /* struct DMAC5 *///FFFE1050
                                                            /* struct DMAC6 *///FFFE1060
                                                            /* struct DMAC7 *///FFFE1070
        void            *SAR;                               /* SAR          *///FFFE1040
        void            *DAR;                               /* DAR          *///FFFE1044
        unsigned int    DMATCR;                             /* DMATCR       *///FFFE1048
        union {                                             /* CHCR         *///FFFE104C
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Word Access */
                unsigned short H;                           /*    High Word */
                unsigned short L;                           /*    Low  Word */
            }           WORD;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char TC            : 1;            /*    TC        */
                unsigned char               : 2;            /*              */
                unsigned char RLD           : 1;            /*    RLD       */
                unsigned char               : 4;            /*              */
                unsigned char               : 4;            /*              */
                unsigned char HE            : 1;            /*    HE        */
                unsigned char HIE           : 1;            /*    HIE       */
                unsigned char               : 2;            /*              */
                unsigned char DM            : 2;            /*    DM        */
                unsigned char SM            : 2;            /*    SM        */
                unsigned char RS            : 4;            /*    RS        */
                unsigned char               : 2;            /*              */
                unsigned char TB            : 1;            /*    TB        */
                unsigned char TS            : 2;            /*    TS        */
                unsigned char IE            : 1;            /*    IE        */
                unsigned char TE            : 1;            /*    TE        */
                unsigned char DE            : 1;            /*    DE        */
            }           BIT;                                /*              */
        }               CHCR;                               /*              */
        char            wk1[240];                           /*              *///FFFE1140-FFFE104C-4
        void            *RSAR;                              /* RSAR         *///FFFE1140
        void            *RDAR;                              /* RDAR         *///FFFE1144
        unsigned int    RDMATCR;                            /* RDMATCR      *///FFFE1148
};                                                          /*              */
struct st_mtu2 {                                            /* struct MTU2  */
        union {                                             /* TOER         *///FFFE420A
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char OE4D          : 1;            /*    OE4D      */
                unsigned char OE4C          : 1;            /*    OE4C      */
                unsigned char OE3D          : 1;            /*    OE3D      */
                unsigned char OE4B          : 1;            /*    OE4B      */
                unsigned char OE4A          : 1;            /*    OE4A      */
                unsigned char OE3B          : 1;            /*    OE3B      */
            }           BIT;                                /*              */
        }               TOER;                               /*              */
        char            wk1[2];                             /*              *///FFFE420D-FFFE420A-1
        union {                                             /* TGCR         *///FFFE420D
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char BDC           : 1;            /*    BDC       */
                unsigned char N             : 1;            /*    N         */
                unsigned char P             : 1;            /*    P         */
                unsigned char FB            : 1;            /*    FB        */
                unsigned char WF            : 1;            /*    WF        */
                unsigned char VF            : 1;            /*    VF        */
                unsigned char UF            : 1;            /*    UF        */
            }           BIT;                                /*              */
        }               TGCR;                               /*              */
        union {                                             /* TOCR1        *///FFFE420E
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PSYE          : 1;            /*    PSYE      */
                unsigned char               : 2;            /*              */
                unsigned char TOCL          : 1;            /*    TOCL      */
                unsigned char TOCS          : 1;            /*    TOCS      */
                unsigned char OLSN          : 1;            /*    OLSN      */
                unsigned char OLSP          : 1;            /*    OLSP      */
            }           BIT;                                /*              */
        }               TOCR1;                              /*              */
        union {                                             /* TOCR2        *///FFFE420F
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char BF            : 2;            /*    BF        */
                unsigned char OLS3N         : 1;            /*    OLS3N     */
                unsigned char OLS3P         : 1;            /*    OLS3P     */
                unsigned char OLS2N         : 1;            /*    OLS2N     */
                unsigned char OLS2P         : 1;            /*    OLS2P     */
                unsigned char OLS1N         : 1;            /*    OLS1N     */
                unsigned char OLS1P         : 1;            /*    OLS1P     */
            }           BIT;                                /*              */
        }               TOCR2;                              /*              */
        char            wk2[4];                             /*              *///FFFE4214-FFFE420F-1
        unsigned short  TCDR;                               /* TCDR         *///FFFE4214
        unsigned short  TDDR;                               /* TDDR         *///FFFE4216
        char            wk3[8];                             /*              *///FFFE4220-FFFE4216-2
        unsigned short  TCNTS;                              /* TCNTS        *///FFFE4220
        unsigned short  TCBR;                               /* TCBR         *///FFFE4222
        char            wk4[12];                            /*              *///FFFE4230-FFFE4222-2
        union {                                             /* TITCR        *///FFFE4230
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char T3AEN         : 1;            /*    T3AEN     */
                unsigned char T3ACOR        : 3;            /*    T3ACOR    */
                unsigned char T4VEN         : 1;            /*    T4VEN     */
                unsigned char T4VCOR        : 3;            /*    T4VCOR    */
            }           BIT;                                /*              */
        }               TITCR;                              /*              */
        union {                                             /* TITCNT       *///FFFE4231
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char T3ACNT        : 3;            /*    T3ACNT    */
                unsigned char               : 1;            /*              */
                unsigned char T4VCNT        : 3;            /*    T4VCNT    */
            }           BIT;                                /*              */
        }               TITCNT;                             /*              */
        union {                                             /* TBTER        *///FFFE4232
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 6;            /*              */
                unsigned char BTE           : 2;            /*    BTE       */
            }           BIT;                                /*              */
        }               TBTER;                              /*              */
        char            wk5[1];                             /*              *///FFFE4234-FFFE4232-1
        union {                                             /* TDER         *///FFFE4234
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 7;            /*              */
                unsigned char TDER          : 1;            /*    TDER      */
            }           BIT;                                /*              */
        }               TDER;                               /*              */
        char            wk6[1];                             /*              *///FFFE4236-FFFE4234-1
        union {                                             /* TOLBR        *///FFFE4236
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char OLS3N         : 1;            /*    OLS3N     */
                unsigned char OLS3P         : 1;            /*    OLS3P     */
                unsigned char OLS2N         : 1;            /*    OLS2N     */
                unsigned char OLS2P         : 1;            /*    OLS2P     */
                unsigned char OLS1N         : 1;            /*    OLS1N     */
                unsigned char OLS1P         : 1;            /*    OLS1P     */
            }           BIT;                                /*              */
        }               TOLBR;                              /*              */
        char            wk7[41];                            /*              *///FFFE4260-FFFE4236-1
        union {                                             /* TWCR         *///FFFE4260
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char CCE           : 1;            /*    CCE       */
                unsigned char               : 5;            /*              */
                unsigned char               : 1;            /*              */
                unsigned char WRE           : 1;            /*    WRE       */
            }           BIT;                                /*              */
        }               TWCR;                               /*              */
        char            wk8[31];                            /*              *///FFFE4280-FFFE4260-1
        union {                                             /* TSTR         *///FFFE4280
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char CST4          : 1;            /*    CST4      */
                unsigned char CST3          : 1;            /*    CST3      */
                unsigned char               : 3;            /*              */
                unsigned char CST2          : 1;            /*    CST2      */
                unsigned char CST1          : 1;            /*    CST1      */
                unsigned char CST0          : 1;            /*    CST0      */
            }           BIT;                                /*              */
        }               TSTR;                               /*              */
        union {                                             /* TSYR         *///FFFE4281
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char SYNC4         : 1;            /*    SYNC4     */
                unsigned char SYNC3         : 1;            /*    SYNC3     */
                unsigned char               : 3;            /*              */
                unsigned char SYNC2         : 1;            /*    SYNC2     */
                unsigned char SYNC1         : 1;            /*    SYNC1     */
                unsigned char SYNC0         : 1;            /*    SYNC0     */
            }           BIT;                                /*              */
        }               TSYR;                               /*              */
        union {                                             /* TCSYSTR      *///FFFE4282
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char SCH0          : 1;            /*    SCH0      */
                unsigned char SCH1          : 1;            /*    SCH1      */
                unsigned char SCH2          : 1;            /*    SCH2      */
                unsigned char SCH3          : 1;            /*    SCH3      */
                unsigned char SCH4          : 1;            /*    SCH4      */
                unsigned char               : 1;            /*              */
                unsigned char SCH3S         : 1;            /*    SCH3S     */
                unsigned char SCH4S         : 1;            /*    SCH4S     */
            }           BIT;                                /*              */
        }               TCSYSTR;                            /*              */
        char            wk9[1];                             /*              *///FFFE4284-FFFE4282-1
        union {                                             /* TRWER        *///FFFE4284
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 7;            /*              */
                unsigned char RWE           : 1;            /*    RWE       */
            }           BIT;                                /*              */
        }               TRWER;                              /*              */
};                                                          /*              */
struct st_mtu20 {                                           /* struct MTU20 */
        union {                                             /* TCR          *///FFFE4300
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char CCLR          : 3;            /*    CCLR      */
                unsigned char CKEG          : 2;            /*    CKEG      */
                unsigned char TPSC          : 3;            /*    TPSC      */
            }           BIT;                                /*              */
        }               TCR;                                /*              */
        union {                                             /* TMDR         *///FFFE4301
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char BFE           : 1;            /*    BFE       */
                unsigned char BFB           : 1;            /*    BFB       */
                unsigned char BFA           : 1;            /*    BFA       */
                unsigned char MD            : 4;            /*    MD        */
            }           BIT;                                /*              */
        }               TMDR;                               /*              */
        union {                                             /* TIOR         *///FFFE4302
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    TIORH     */
                unsigned char L;                            /*    TIORL     */
                }       BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char IOB           : 4;            /*    IOB       */
                unsigned char IOA           : 4;            /*    IOA       */
                unsigned char IOD           : 4;            /*    IOD       */
                unsigned char IOC           : 4;            /*    IOC       */
            }           BIT;                                /*              */
        }               TIOR;                               /*              */
        union {                                             /* TIER         *///FFFE4304
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char TTGE          : 1;            /*    TTGE      */
                unsigned char               : 2;            /*              */
                unsigned char TCIEV         : 1;            /*    TCIEV     */
                unsigned char TGIED         : 1;            /*    TGIED     */
                unsigned char TGIEC         : 1;            /*    TGIEC     */
                unsigned char TGIEB         : 1;            /*    TGIEB     */
                unsigned char TGIEA         : 1;            /*    TGIEA     */
            }           BIT;                                /*              */
        }               TIER;                               /*              */
        union {                                             /* TSR          *///FFFE4305
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 3;            /*              */
                unsigned char TCFV          : 1;            /*    TCFV      */
                unsigned char TGFD          : 1;            /*    TGFD      */
                unsigned char TGFC          : 1;            /*    TGFC      */
                unsigned char TGFB          : 1;            /*    TGFB      */
                unsigned char TGFA          : 1;            /*    TGFA      */
            }           BIT;                                /*              */
        }               TSR;                                /*              */
        unsigned short  TCNT;                               /* TCNT         *///FFFE4306
        unsigned short  TGRA;                               /* TGRA         *///FFFE4308
        unsigned short  TGRB;                               /* TGRB         *///FFFE430A
        unsigned short  TGRC;                               /* TGRC         *///FFFE430C
        unsigned short  TGRD;                               /* TGRD         *///FFFE430E
        char            wk1[16];                            /*              *///FFFE4320-FFFE430E-2
        unsigned short  TGRE;                               /* TGRE         *///FFFE4320
        unsigned short  TGRF;                               /* TGRF         *///FFFE4322
        union {                                             /* TIER2        *///FFFE4324
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char TTGE2         : 1;            /*    TTGE2     */
                unsigned char               : 5;            /*              */
                unsigned char TGIEF         : 1;            /*    TGIEF     */
                unsigned char TGIEE         : 1;            /*    TGIEE     */
            }           BIT;                                /*              */
        }               TIER2;                              /*              */
        union {                                             /* TSR2         *///FFFE4325
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 6;            /*              */
                unsigned char TGFF          : 1;            /*    TGFF      */
                unsigned char TGFE          : 1;            /*    TGFE      */
            }           BIT;                                /*              */
        }               TSR2;                               /*              */
        union {                                             /* TBTM         *///FFFE4326
                unsigned char BYTE;                         /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char TTSE          : 1;            /*    TTSE      */
                unsigned char TTSB          : 1;            /*    TTSB      */
                unsigned char TTSA          : 1;            /*    TTSA      */
            }           BIT;                                /*              */
        }               TBTM;                               /*              */
};                                                          /*              */
struct st_mtu21 {                                           /* struct MTU21 */
        union {                                             /* TCR          *///FFFE4380
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char CCLR          : 2;            /*    CCLR      */
                unsigned char CKEG          : 2;            /*    CKEG      */
                unsigned char TPSC          : 3;            /*    TPSC      */
            }           BIT;                                /*              */
        }               TCR;                                /*              */
        union {                                             /* TMDR         *///FFFE4381
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 4;            /*              */
                unsigned char MD            : 4;            /*    MD        */
            }           BIT;                                /*              */
        }               TMDR;                               /*              */
        union {                                             /* TIOR         *///FFFE4382
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char IOB           : 4;            /*    IOB       */
                unsigned char IOA           : 4;            /*    IOA       */
            }           BIT;                                /*              */
        }               TIOR;                               /*              */
        char            wk1[1];                             /*              *///FFFE4384-FFFE4382-1
        union {                                             /* TIER         *///FFFE4384
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char TTGE          : 1;            /*    TTGE      */
                unsigned char               : 1;            /*              */
                unsigned char TCIEU         : 1;            /*    TCIEU     */
                unsigned char TCIEV         : 1;            /*    TCIEV     */
                unsigned char               : 2;            /*              */
                unsigned char TGIEB         : 1;            /*    TGIEB     */
                unsigned char TGIEA         : 1;            /*    TGIEA     */
            }           BIT;                                /*              */
        }               TIER;                               /*              */
        union {                                             /* TSR          *///FFFE4385
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char TCFD          : 1;            /*    TCFD      */
                unsigned char               : 1;            /*              */
                unsigned char TCFU          : 1;            /*    TCFU      */
                unsigned char TCFV          : 1;            /*    TCFV      */
                unsigned char               : 2;            /*              */
                unsigned char TGFB          : 1;            /*    TGFB      */
                unsigned char TGFA          : 1;            /*    TGFA      */
            }           BIT;                                /*              */
        }               TSR;                                /*              */
        unsigned short  TCNT;                               /* TCNT         *///FFFE4386
        unsigned short  TGRA;                               /* TGRA         *///FFFE4388
        unsigned short  TGRB;                               /* TGRB         *///FFFE438A
        char            wk2[4];                             /*              *///FFFE4390-FFFE438A-2
        union {                                             /* TICCR        *///FFFE4390
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 4;            /*              */
                unsigned char I2BE          : 1;            /*    I2BE      */
                unsigned char I2AE          : 1;            /*    I2AE      */
                unsigned char I1BE          : 1;            /*    I1BE      */
                unsigned char I1AE          : 1;            /*    I1AE      */
            }           BIT;                                /*              */
        }               TICCR;                              /*              */
};                                                          /*              */
struct st_mtu22 {                                           /* struct MTU22 */
        union {                                             /* TCR          *///FFFE4000
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char CCLR          : 2;            /*    CCLR      */
                unsigned char CKEG          : 2;            /*    CKEG      */
                unsigned char TPSC          : 3;            /*    TPSC      */
            }           BIT;                                /*              */
        }               TCR;                                /*              */
        union {                                             /* TMDR         *///FFFE4001
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 4;            /*              */
                unsigned char MD            : 4;            /*    MD        */
            }           BIT;                                /*              */
        }               TMDR;                               /*              */
        union {                                             /* TIOR         *///FFFE4002
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char IOB           : 4;            /*    IOB       */
                unsigned char IOA           : 4;            /*    IOA       */
            }           BIT;                                /*              */
        }               TIOR;                               /*              */
        char            wk1[1];                             /*              *///FFFE4004-FFFE4002-1
        union {                                             /* TIER         *///FFFE4004
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char TTGE          : 1;            /*    TTGE      */
                unsigned char               : 1;            /*              */
                unsigned char TCIEU         : 1;            /*    TCIEU     */
                unsigned char TCIEV         : 1;            /*    TCIEV     */
                unsigned char               : 2;            /*              */
                unsigned char TGIEB         : 1;            /*    TGIEB     */
                unsigned char TGIEA         : 1;            /*    TGIEA     */
            }           BIT;                                /*              */
        }               TIER;                               /*              */
        union {                                             /* TSR          *///FFFE4005
                unsigned char BYTE;                         /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char TCFD          : 1;            /*    TCFD      */
                unsigned char               : 1;            /*              */
                unsigned char TCFU          : 1;            /*    TCFU      */
                unsigned char TCFV          : 1;            /*    TCFV      */
                unsigned char               : 2;            /*              */
                unsigned char TGFB          : 1;            /*    TGFB      */
                unsigned char TGFA          : 1;            /*    TGFA      */
            }           BIT;                                /*              */
        }               TSR;                                /*              */
        unsigned short  TCNT;                               /* TCNT         *///FFFE4006
        unsigned short  TGRA;                               /* TGRA         *///FFFE4008
        unsigned short  TGRB;                               /* TGRB         *///FFFE400A
};                                                          /*              */
struct st_mtu23 {                                           /* struct MTU23 */
        union {                                             /* TCR          *///FFFE4200
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char CCLR          : 3;            /*    CCLR      */
                unsigned char CKEG          : 2;            /*    CKEG      */
                unsigned char TPSC          : 3;            /*    TPSC      */
            }           BIT;                                /*              */
        }               TCR;                                /*              */
        char            wk1[1];                             /*              *///FFFE4202-FFFE4200-1
        union {                                             /* TMDR         *///FFFE4202
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char BFB           : 1;            /*    BFB       */
                unsigned char BFA           : 1;            /*    BFA       */
                unsigned char MD            : 4;            /*    MD        */
            }           BIT;                                /*              */
        }               TMDR;                               /*              */
        char            wk2[1];                             /*              *///FFFE4204-FFFE4202-1
        union {                                             /* TIOR         *///FFFE4204
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    TIORH     */
                unsigned char L;                            /*    TIORL     */
            }       BYTE;                                   /*              */
            struct {                                        /*  Bit Access  */
                unsigned char IOB           : 4;            /*    IOB       */
                unsigned char IOA           : 4;            /*    IOA       */
                unsigned char IOD           : 4;            /*    IOD       */
                unsigned char IOC           : 4;            /*    IOC       */
            }           BIT;                                /*              */
        }               TIOR;                               /*              */
        char            wk3[2];                             /*              *///FFFE4208-FFFE4204-2
        union {                                             /* TIER         *///FFFE4208
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char TTGE          : 1;            /*    TTGE      */
                unsigned char               : 2;            /*              */
                unsigned char TCIEV         : 1;            /*    TCIEV     */
                unsigned char TGIED         : 1;            /*    TGIED     */
                unsigned char TGIEC         : 1;            /*    TGIEC     */
                unsigned char TGIEB         : 1;            /*    TGIEB     */
                unsigned char TGIEA         : 1;            /*    TGIEA     */
            }           BIT;                                /*              */
        }               TIER;                               /*              */
        char            wk4[7];                             /*              *///FFFE4210-FFFE4208-1
        unsigned short  TCNT;                               /* TCNT         *///FFFE4210
        char            wk5[6];                             /*              *///FFFE4218-FFFE4210-2
        unsigned short  TGRA;                               /* TGRA         *///FFFE4218
        unsigned short  TGRB;                               /* TGRB         *///FFFE421A
        char            wk6[8];                             /*              *///FFFE4224-FFFE421A-2
        unsigned short  TGRC;                               /* TGRC         *///FFFE4224
        unsigned short  TGRD;                               /* TGRD         *///FFFE4226
        char            wk7[4];                             /*              *///FFFE422C-FFFE4226-2
        union {                                             /* TSR          *///FFFE422C
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char TCFD          : 1;            /*    TCFD      */
                unsigned char               : 2;            /*              */
                unsigned char TCFV          : 1;            /*    TCFV      */
                unsigned char TGFD          : 1;            /*    TGFD      */
                unsigned char TGFC          : 1;            /*    TGFC      */
                unsigned char TGFB          : 1;            /*    TGFB      */
                unsigned char TGFA          : 1;            /*    TGFA      */
            }           BIT;                                /*              */
        }               TSR;                                /*              */
        char            wk8[11];                            /*              *///FFFE4238-FFFE422C-1
        union {                                             /* TBTM         *///FFFE4238
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 6;            /*              */
                unsigned char TTSB          : 1;            /*    TTSB      */
                unsigned char TTSA          : 1;            /*    TTSA      */
            }           BIT;                                /*              */
        }               TBTM;                               /*              */
};                                                          /*              */
struct st_mtu24 {                                           /* struct MTU24 */
        char            wk1[1];                             /*              *///FFFE4200
        union {                                             /* TCR          *///FFFE4201
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char CCLR          : 3;            /*    CCLR      */
                unsigned char CKEG          : 2;            /*    CKEG      */
                unsigned char TPSC          : 3;            /*    TPSC      */
            }           BIT;                                /*              */
        }               TCR;                                /*              */
        char            wk2[1];                             /*              *///FFFE4203-FFFE4201-1
        union {                                             /* TMDR         *///FFFE4203
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char BFB           : 1;            /*    BFB       */
                unsigned char BFA           : 1;            /*    BFA       */
                unsigned char MD            : 4;            /*    MD        */
            }           BIT;                                /*              */
        }               TMDR;                               /*              */
        char            wk3[2];                             /*              *///FFFE4206-FFFE4203-1
        union {                                             /* TIOR         *///FFFE4206
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    TIORH     */
                unsigned char L;                            /*    TIORL     */
            }       BYTE;                                   /*              */
            struct {                                        /*  Bit Access  */
                unsigned char IOB           : 4;            /*    IOB       */
                unsigned char IOA           : 4;            /*    IOA       */
                unsigned char IOD           : 4;            /*    IOD       */
                unsigned char IOC           : 4;            /*    IOC       */
            }           BIT;                                /*              */
        }               TIOR;                               /*              */
        char            wk4[1];                             /*              *///FFFE4209-FFFE4206-2
        union {                                             /* TIER         *///FFFE4209
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char TTGE          : 1;            /*    TTGE      */
                unsigned char TTGE2         : 1;            /*    TTGE2     */
                unsigned char               : 1;            /*              */
                unsigned char TCIEV         : 1;            /*    TCIEV     */
                unsigned char TGIED         : 1;            /*    TGIED     */
                unsigned char TGIEC         : 1;            /*    TGIEC     */
                unsigned char TGIEB         : 1;            /*    TGIEB     */
                unsigned char TGIEA         : 1;            /*    TGIEA     */
            }           BIT;                                /*              */
        }               TIER;                               /*              */
        char            wk5[8];                             /*              *///FFFE4212-FFFE4209-1
        unsigned short  TCNT;                               /* TCNT         *///FFFE4212
        char            wk6[8];                             /*              *///FFFE421C-FFFE4212-2
        unsigned short  TGRA;                               /* TGRA         *///FFFE421C
        unsigned short  TGRB;                               /* TGRB         *///FFFE421E
        char            wk7[8];                             /*              *///FFFE4228-FFFE421E-2
        unsigned short  TGRC;                               /* TGRC         *///FFFE4228
        unsigned short  TGRD;                               /* TGRD         *///FFFE422A
        char            wk8[1];                             /*              *///FFFE422D-FFFE422A-2
        union {                                             /* TSR          *///FFFE422D
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char TCFD          : 1;            /*    TCFD      */
                unsigned char               : 2;            /*              */
                unsigned char TCFV          : 1;            /*    TCFV      */
                unsigned char TGFD          : 1;            /*    TGFD      */
                unsigned char TGFC          : 1;            /*    TGFC      */
                unsigned char TGFB          : 1;            /*    TGFB      */
                unsigned char TGFA          : 1;            /*    TGFA      */
            }           BIT;                                /*              */
        }               TSR;                                /*              */
        char            wk9[11];                            /*              *///FFFE4239-FFFE422D-1
        union {                                             /* TBTM         *///FFFE4239
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 6;            /*              */
                unsigned char TTSB          : 1;            /*    TTSB      */
                unsigned char TTSA          : 1;            /*    TTSA      */
            }           BIT;                                /*              */
        }               TBTM;                               /*              */
        char            wk10[6];                            /*              *///FFFE4240-FFFE4239-1
        union {                                             /* TADCR        *///FFFE4240
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short BF           : 2;            /*    BF        */
                unsigned short              : 6;            /*              */
                unsigned short UT4AE        : 1;            /*    UT4AE     */
                unsigned short DT4AE        : 1;            /*    DT4AE     */
                unsigned short UT4BE        : 1;            /*    UT4BE     */
                unsigned short DT4BE        : 1;            /*    DT4BE     */
                unsigned short ITA3AE       : 1;            /*    ITA3AE    */
                unsigned short ITA4VE       : 1;            /*    ITA4VE    */
                unsigned short ITB3AE       : 1;            /*    ITB3AE    */
                unsigned short ITB4VE       : 1;            /*    ITB4VE    */
            }           BIT;                                /*              */
        }               TADCR;                              /*              */
        char            wk11[2];                            /*              *///FFFE4244-FFFE4240-2
        unsigned short  TADCORA;                            /* TADCORA      *///FFFE4244
        unsigned short  TADCORB;                            /* TADCORB      *///FFFE4246
        unsigned short  TADCOBRA;                           /* TADCOBRA     *///FFFE4248
        unsigned short  TADCOBRB;                           /* TADCOBRB     *///FFFE424A
};                                                          /*              */
struct st_mtu25 {                                           /* struct MTU25 */
        unsigned short  TCNTU;                              /* TCNTU        *///FFFE4080
        unsigned short  TGRU;                               /* TGRU         *///FFFE4082
        union {                                             /* TCRU         *///FFFE4084
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 6;            /*              */
                unsigned char TPSC          : 2;            /*    TPSC      */
            }           BIT;                                /*              */
        }               TCRU;                               /*              */
        char            wk1[1];                             /*              *///FFFE4086-FFFE4084-1
        union {                                             /* TIORU        *///FFFE4086
                unsigned char BYTE;                         /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 3;            /*              */
                unsigned char IOC           : 5;            /*    IOC       */
            }           BIT;                                /*              */
        }               TIORU;                              /*              */
        char            wk2[9];                             /*              *///FFFE4090-FFFE4086-1
        unsigned short  TCNTV;                              /* TCNTV        *///FFFE4090
        unsigned short  TGRV;                               /* TGRV         *///FFFE4092
        union {                                             /* TCRV         *///FFFE4094
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 6;            /*              */
                unsigned char TPSC          : 2;            /*    TPSC      */
            }           BIT;                                /*              */
        }               TCRV;                               /*              */
        char            wk3[1];                             /*              *///FFFE4096-FFFE4094-1
        union {                                             /* TIORV        *///FFFE4096
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 3;            /*              */
                unsigned char IOC           : 5;            /*    IOC       */
            }           BIT;                                /*              */
        }               TIORV;                              /*              */
        char            wk4[9];                             /*              *///FFFE40A0-FFFE4096-1
        unsigned short  TCNTW;                              /* TCNTW        *///FFFE40A0
        unsigned short  TGRW;                               /* TGRW         *///FFFE40A2
        union {                                             /* TCRW         *///FFFE40A4
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 6;            /*              */
                unsigned char TPSC          : 2;            /*    TPSC      */
            }           BIT;                                /*              */
        }               TCRW;                               /*              */
        char            wk5[1];                             /*              *///FFFE40A6-FFFE40A4-1
        union {                                             /* TIORW        *///FFFE40A6
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 3;            /*              */
                unsigned char IOC           : 5;            /*    IOC       */
            }           BIT;                                /*              */
        }               TIORW;                              /*              */
        char            wk6[9];                             /*              *///FFFE40B0-FFFE40A6-1
        union {                                             /* TSR          *///FFFE40B0
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char CMFU          : 1;            /*    CMFU      */
                unsigned char CMFV          : 1;            /*    CMFV      */
                unsigned char CMFW          : 1;            /*    CMFW      */
            }           BIT;                                /*              */
        }               TSR;                                /*              */
        char            wk7[1];                             /*              *///FFFE40B2-FFFE40B0-1
        union {                                             /* TIER         *///FFFE40B2
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char TGIEU         : 1;            /*    TGIEU     */
                unsigned char TGIEV         : 1;            /*    TGIEV     */
                unsigned char TGIEW         : 1;            /*    TGIEW     */
            }           BIT;                                /*              */
        }               TIER;                               /*              */
        char            wk8[1];                             /*              *///FFFE40B4-FFFE40B2-1
        union {                                             /* TSTR         *///FFFE40B4
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char CSTU          : 1;            /*    CSTU      */
                unsigned char CSTV          : 1;            /*    CSTV      */
                unsigned char CSTW          : 1;            /*    CSTW      */
            }           BIT;                                /*              */
        }               TSTR;                               /*              */
        char            wk9[1];                             /*              *///FFFE40B6-FFFE40B4-1
        union {                                             /* TCNTCMPCLR   *///FFFE40B6
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char CLRU          : 1;            /*    CLRU      */
                unsigned char CLRV          : 1;            /*    CLRV      */
                unsigned char CLRW          : 1;            /*    CLRW      */
            }           BIT;                                /*              */
        }               TCNTCMPCLR;                         /*              */
};                                                          /*              */
struct st_mtu2s {                                           /* struct MTU2S */
        union {                                             /* TOERS        *///FFFE4A0A
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char OE4D          : 1;            /*    OE4D      */
                unsigned char OE4C          : 1;            /*    OE4C      */
                unsigned char OE3D          : 1;            /*    OE3D      */
                unsigned char OE4B          : 1;            /*    OE4B      */
                unsigned char OE4A          : 1;            /*    OE4A      */
                unsigned char OE3B          : 1;            /*    OE3B      */
            }           BIT;                                /*              */
        }               TOER;                               /*              */
        char            wk1[2];                             /*              *///FFFE4A0D-FFFE4A0A-1
        union {                                             /* TGCRS        *///FFFE4A0D
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char BDC           : 1;            /*    BDC       */
                unsigned char N             : 1;            /*    N         */
                unsigned char P             : 1;            /*    P         */
                unsigned char FB            : 1;            /*    FB        */
                unsigned char WF            : 1;            /*    WF        */
                unsigned char VF            : 1;            /*    VF        */
                unsigned char UF            : 1;            /*    UF        */
            }           BIT;                                /*              */
        }               TGCR;                               /*              */
        union {                                             /* TOCR1S       *///FFFE4A0E
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PSYE          : 1;            /*    PSYE      */
                unsigned char               : 2;            /*              */
                unsigned char TOCL          : 1;            /*    TOCL      */
                unsigned char TOCS          : 1;            /*    TOCS      */
                unsigned char OLSN          : 1;            /*    OLSN      */
                unsigned char OLSP          : 1;            /*    OLSP      */
            }           BIT;                                /*              */
        }               TOCR1;                              /*              */
        union {                                             /* TOCR2S       *///FFFE4A0F
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char BF            : 2;            /*    BF        */
                unsigned char OLS3N         : 1;            /*    OLS3N     */
                unsigned char OLS3P         : 1;            /*    OLS3P     */
                unsigned char OLS2N         : 1;            /*    OLS2N     */
                unsigned char OLS2P         : 1;            /*    OLS2P     */
                unsigned char OLS1N         : 1;            /*    OLS1N     */
                unsigned char OLS1P         : 1;            /*    OLS1P     */
            }           BIT;                                /*              */
        }               TOCR2;                              /*              */
        char            wk2[4];                             /*              *///FFFE4A14-FFFE4A0F-1
        unsigned short  TCDR;                               /* TCDRS        *///FFFE4A14
        unsigned short  TDDR;                               /* TDDRS        *///FFFE4A16
        char            wk3[8];                             /*              *///FFFE4A20-FFFE4A16-2
        unsigned short  TCNTS;                              /* TCNTS        *///FFFE4A20
        unsigned short  TCBR;                               /* TCBRS        *///FFFE4A22
        char            wk4[12];                            /*              *///FFFE4A30-FFFE4A22-2
        union {                                             /* TITCRS       *///FFFE4A30
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char T3AEN         : 1;            /*    T3AEN     */
                unsigned char T3ACOR        : 3;            /*    T3ACOR    */
                unsigned char T4VEN         : 1;            /*    T4VEN     */
                unsigned char T4VCOR        : 3;            /*    T4VCOR    */
            }           BIT;                                /*              */
        }               TITCR;                              /*              */
        union {                                             /* TITCNTS      *///FFFE4A31
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char T3ACNT        : 3;            /*    T3ACNT    */
                unsigned char               : 1;            /*              */
                unsigned char T4VCNT        : 3;            /*    T4VCNT    */
            }           BIT;                                /*              */
        }               TITCNT;                             /*              */
        union {                                             /* TBTERS       *///FFFE4A32
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 6;            /*              */
                unsigned char BTE           : 2;            /*    BTE       */
            }           BIT;                                /*              */
        }               TBTER;                              /*              */
        char            wk5[1];                             /*              *///FFFE4A34-FFFE4A32-1
        union {                                             /* TDER         *///FFFE4A34
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 7;            /*              */
                unsigned char TDER          : 1;            /*    TDER      */
            }           BIT;                                /*              */
        }               TDER;                               /*              */
        char            wk6[1];                             /*              *///FFFE4A36-FFFE4A34-1
        union {                                             /* TOLBR        *///FFFE4A36
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char OLS3N         : 1;            /*    OLS3N     */
                unsigned char OLS3P         : 1;            /*    OLS3P     */
                unsigned char OLS2N         : 1;            /*    OLS2N     */
                unsigned char OLS2P         : 1;            /*    OLS2P     */
                unsigned char OLS1N         : 1;            /*    OLS1N     */
                unsigned char OLS1P         : 1;            /*    OLS1P     */
            }           BIT;                                /*              */
        }               TOLBR;                              /*              */
        char            wk7[25];                            /*              *///FFFE4A50-FFFE4A36-1
        union {                                             /* TSYCRS       *///FFFE4A50
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char CE0A          : 1;            /*    CE0A      */
                unsigned char CE0B          : 1;            /*    CE0B      */
                unsigned char CE0C          : 1;            /*    CE0C      */
                unsigned char CE0D          : 1;            /*    CE0D      */
                unsigned char CE1A          : 1;            /*    CE1A      */
                unsigned char CE1B          : 1;            /*    CE1B      */
                unsigned char CE2A          : 1;            /*    CE2A      */
                unsigned char CE2B          : 1;            /*    CE2B      */
            }           BIT;                                /*              */
        }               TSYCRS;                             /*              */
        char            wk8[15];                            /*              *///FFFE4A60-FFFE4A50-1
        union {                                             /* TWCRS        *///FFFE4A60
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char CCE           : 1;            /*    CCE       */
                unsigned char               : 5;            /*              */
                unsigned char SCC           : 1;            /*    SCC       */
                unsigned char WRE           : 1;            /*    WRE       */
            }           BIT;                                /*              */
        }               TWCR;                               /*              */
        char            wk9[31];                            /*              *///FFFE4A80-FFFE4A60-1
        union {                                             /* TSTRS        *///FFFE4A80
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char CST4          : 1;            /*    CST4      */
                unsigned char CST3          : 1;            /*    CST3      */
                unsigned char               : 3;            /*              */
                unsigned char CST2          : 1;            /*    CST2      */
                unsigned char CST1          : 1;            /*    CST1      */
                unsigned char CST0          : 1;            /*    CST0      */
            }           BIT;                                /*              */
        }               TSTR;                               /*              */
        union {                                             /* TSYRS        *///FFFE4A81
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char SYNC4         : 1;            /*    SYNC4     */
                unsigned char SYNC3         : 1;            /*    SYNC3     */
                unsigned char               : 3;            /*              */
                unsigned char SYNC2         : 1;            /*    SYNC2     */
                unsigned char SYNC1         : 1;            /*    SYNC1     */
                unsigned char SYNC0         : 1;            /*    SYNC0     */
            }           BIT;                                /*              */
        }               TSYR;                               /*              */
        char            wk10[2];                            /*              *///FFFE4A84-FFFE4A81-1
        union {                                             /* TRWERS       *///FFFE4A84
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 7;            /*              */
                unsigned char RWE           : 1;            /*    RWE       */
            }           BIT;                                /*              */
        }               TRWER;                              /*              */
};                                                          /*              */
struct st_poe2 {                                            /* struct POE2  */
        union {                                             /* ICSR1        *///FFFE5000
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short POE3F        : 1;            /*    POE3F     */
                unsigned short POE2F        : 1;            /*    POE2F     */
                unsigned short POE1F        : 1;            /*    POE1F     */
                unsigned short POE0F        : 1;            /*    POE0F     */
                unsigned short              : 3;            /*              */
                unsigned short PIE1         : 1;            /*    PIE1      */
                unsigned short POE3M        : 2;            /*    POE3M     */
                unsigned short POE2M        : 2;            /*    POE2M     */
                unsigned short POE1M        : 2;            /*    POE1M     */
                unsigned short POE0M        : 2;            /*    POE0M     */
            }           BIT;                                /*              */
        }               ICSR1;                              /*              */
        union {                                             /* OCSR1        *///FFFE5002
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short OSF1         : 1;            /*    OSF1      */
                unsigned short              : 5;            /*              */
                unsigned short OCE1         : 1;            /*    OCE1      */
                unsigned short OIE1         : 1;            /*    OIE1      */
            }           BIT;                                /*              */
        }               OCSR1;                              /*              */
        union {                                             /* ICSR2        *///FFFE5004
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short              : 3;            /*              */
                unsigned short POE4F        : 1;            /*    POE4F     */
                unsigned short              : 3;            /*              */
                unsigned short PIE2         : 1;            /*    PIE2      */
                unsigned short              : 6;            /*              */
                unsigned short POE4M        : 2;            /*    POE4M     */
            }           BIT;                                /*              */
        }               ICSR2;                              /*              */
        union {                                             /* OCSR2        *///FFFE5006
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short OSF2         : 1;            /*    OSF2      */
                unsigned short              : 5;            /*              */
                unsigned short OCE2         : 1;            /*    OCE2      */
                unsigned short OIE2         : 1;            /*    OIE2      */
            }           BIT;                                /*              */
        }               OCSR2;                              /*              */
        union {                                             /* ICSR3        *///FFFE5008
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short              : 3;            /*              */
                unsigned short POE8F        : 1;            /*    POE8F     */
                unsigned short              : 2;            /*              */
                unsigned short POE8E        : 1;            /*    POE8E     */
                unsigned short PIE3         : 1;            /*    PIE3      */
                unsigned short              : 6;            /*              */
                unsigned short POE8M        : 2;            /*    POE8M     */
            }           BIT;                                /*              */
        }               ICSR3;                              /*              */
        union {                                             /* SPOER        *///FFFE500A
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char MTU2SHIZ      : 1;            /*    MTU2SHIZ  */
                unsigned char MTU2CH0HIZ    : 1;            /*    MTU2CH0HIZ*/
                unsigned char MTU2CH34HIZ   : 1;            /*    MTU2CH34HI*/
            }           BIT;                                /*              */
        }               SPOER;                              /*              */
        union {                                             /* POECR1       *///FFFE500B
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char MTU2PB4ZE     : 1;            /*    MTU2PB4ZE */
                unsigned char MTU2PB3ZE     : 1;            /*    MTU2PB3ZE */
                unsigned char MTU2PB2ZE     : 1;            /*    MTU2PB2ZE */
                unsigned char MTU2PB1ZE     : 1;            /*    MTU2PB1ZE */
                unsigned char MTU2PE3ZE     : 1;            /*    MTU2PE3ZE */
                unsigned char MTU2PE2ZE     : 1;            /*    MTU2PE2ZE */
                unsigned char MTU2PE1ZE     : 1;            /*    MTU2PE1ZE */
                unsigned char MTU2PE0ZE     : 1;            /*    MTU2PE0ZE */
            }           BIT;                                /*              */
        }               POECR1;                             /*              */
        union {                                             /* POECR2       *///FFFE500C
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short              : 1;            /*              */
                unsigned short MTU2P1CZE    : 1;            /*    MTU2P1CZE */
                unsigned short MTU2P2CZE    : 1;            /*    MTU2P2CZE */
                unsigned short MTU2P3CZE    : 1;            /*    MTU2P3CZE */
                unsigned short              : 1;            /*              */
                unsigned short MTU2SP1CZE   : 1;            /*    MTU2SP1CZE*/
                unsigned short MTU2SP2CZE   : 1;            /*    MTU2SP2CZE*/
                unsigned short MTU2SP3CZE   : 1;            /*    MTU2SP3CZE*/
                unsigned short              : 1;            /*              */
                unsigned short MTU2SP4CZE   : 1;            /*    MTU2SP4CZE*/
                unsigned short MTU2SP5CZE   : 1;            /*    MTU2SP5CZE*/
                unsigned short MTU2SP6CZE   : 1;            /*    MTU2SP6CZE*/
                unsigned short              : 1;            /*              */
                unsigned short MTU2SP7CZE   : 1;            /*    MTU2SP7CZE*/
                unsigned short MTU2SP8CZE   : 1;            /*    MTU2SP8CZE*/
                unsigned short MTU2SP9CZE   : 1;            /*    MTU2SP9CZE*/
            }           BIT;                                /*              */
        }               POECR2;                             /*              */
};                                                          /*              */
struct st_cmt {                                             /* struct CMT   */
        union {                                             /* CMSTR        *///FFFEC000
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short              :14;            /*              */
                unsigned short STR1         : 1;            /*    STR1      */
                unsigned short STR0         : 1;            /*    STR0      */
            }           BIT;                                /*              */
        }               CMSTR;                              /*              */
};                                                          /*              */
struct st_cmt0 {                                            /* struct CMT0  */
        union {                                             /* CMCSR        *///FFFEC002/FFFEC008
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short              : 8;            /*              */
                unsigned short CMF          : 1;            /*    CMF       */
                unsigned short CMIE         : 1;            /*    CMIE      */
                unsigned short              : 4;            /*              */
                unsigned short CKS          : 2;            /*    CKS       */
            }           BIT;                                /*              */
        }               CMCSR;                              /*              */
        unsigned short  CMCNT;                              /* CMCNT        *///FFFEC004/FFFEC00A
        unsigned short  CMCOR;                              /* CMCOR        *///FFFEC006/FFFEC00C
};                                                          /*              */
union un_wdt {                                              /* union WDT    */
    struct {                                                /* Read Access  */
        union {                                             /* WTCSR        *///FFFE0000
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char IOVF          : 1;            /*    IOVF      */
                unsigned char WTIT          : 1;            /*    WT/IT     */
                unsigned char TME           : 1;            /*    TME       */
                unsigned char               : 2;            /*              */
                unsigned char CKS           : 3;            /*    CKS       */
            }           BIT;                                /*              */
        }               WTCSR;                              /*              */
        char            wk1[1];                             /*              *///FFFE0002-FFFE0000-1
        unsigned char   WTCNT;                              /* WTCNT        *///FFFE0002
        char            wk2[1];                             /*              *///FFFE0004-FFFE0002-1
        union {                                             /* WRCSR        *///FFFE0004
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char WOVF          : 1;            /*    WOVF      */
                unsigned char RSTE          : 1;            /*    RSTE      */
                unsigned char RSTS          : 1;            /*    RSTS      */
            }           BIT;                                /*              */
        }               WRCSR;                              /*              */
    } READ;                                                 /*              */
    struct {                                                /* Write Access */
        unsigned short  WTCSR;                              /* WTCSR        *///FFFE0000
        unsigned short  WTCNT;                              /* WTCNT        *///FFFE0002
        unsigned short  WRCSR;                              /* WRCSR        *///FFFE0004
    } WRITE;                                                /*              */
};                                                          /*              */
struct st_sci {                                             /* struct SCI   */
        union {                                             /* SCSMR        *///FFFF8000
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char CA            : 1;            /*    C/A       */
                unsigned char CHR           : 1;            /*    CHR       */
                unsigned char _PE           : 1;            /*    PE        */
                unsigned char OE            : 1;            /*    O/E       */
                unsigned char STOP          : 1;            /*    STOP      */
                unsigned char MP            : 1;            /*    MP        */
                unsigned char CKS           : 2;            /*    CKS       */
            }           BIT;                                /*              */
        }               SCSMR;                              /*              */
        char            wk1[1];                             /*              *///FFFF8002-FFFF8000-1
        unsigned char   SCBRR;                              /* SCBRR        *///FFFF8002
        char            wk2[1];                             /*              *///FFFF8004-FFFF8002-1
        union {                                             /* SCSCR        *///FFFF8004
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char TIE           : 1;            /*    TIE       */
                unsigned char RIE           : 1;            /*    RIE       */
                unsigned char TE            : 1;            /*    TE        */
                unsigned char RE            : 1;            /*    RE        */
                unsigned char MPIE          : 1;            /*    MPIE      */
                unsigned char TEIE          : 1;            /*    TEIE      */
                unsigned char CKE           : 2;            /*    CKE       */
            }           BIT;                                /*              */
        }               SCSCR;                              /*              */
        char            wk3[1];                             /*              *///FFFF8006-FFFF8004-1
        unsigned char   SCTDR;                              /* SCTDR        *///FFFF8006
        char            wk4[1];                             /*              *///FFFF8008-FFFF8006-1
        union {                                             /* SCSSR        *///FFFF8008
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char TDRE          : 1;            /*    TDRE      */
                unsigned char RDRF          : 1;            /*    RDRF      */
                unsigned char ORER          : 1;            /*    ORER      */
                unsigned char FER           : 1;            /*    FER       */
                unsigned char PER           : 1;            /*    PER       */
                unsigned char TEND          : 1;            /*    TEND      */
                unsigned char MPB           : 1;            /*    MPB       */
                unsigned char MPBT          : 1;            /*    MPBT      */
            }           BIT;                                /*              */
        }               SCSSR;                              /*              */
        char            wk5[1];                             /*              *///FFFF800A-FFFF8008-1
        unsigned char   SCRDR;                              /* SCRDR        *///FFFF800A
        char            wk6[1];                             /*              *///FFFF800C-FFFF800A-1
        union {                                             /* SCSDCR       *///FFFF800C
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 4;            /*              */
                unsigned char DIR           : 1;            /*    DIR       */
            }           BIT;                                /*              */
        }               SCSDCR;                             /*              */
        char            wk7[1];                             /*              *///FFFF800E-FFFF800C-1
        union {                                             /* SCSPTR       *///FFFF800E
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char EIO           : 1;            /*    EIO       */
                unsigned char               : 3;            /*              */
                unsigned char SPB1IO        : 1;            /*    SPB1IO    */
                unsigned char SPB1DT        : 1;            /*    SPB1DT    */
                unsigned char               : 1;            /*              */
                unsigned char SPB0DT        : 1;            /*    SPB0DT    */
            }           BIT;                                /*              */
        }               SCSPTR;                             /*              */
};                                                          /*              */
struct st_scif {                                            /* struct SCIF  */
        union {                                             /* SCSMR        *///FFFE9800
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short              : 8;            /*              */
                unsigned short CA           : 1;            /*    C/A       */
                unsigned short CHR          : 1;            /*    CHR       */
                unsigned short _PE          : 1;            /*    PE        */
                unsigned short OE           : 1;            /*    O/E       */
                unsigned short STOP         : 1;            /*    STOP      */
                unsigned short              : 1;            /*              */
                unsigned short CKS          : 2;            /*    CKS       */
            }           BIT;                                /*              */
        }               SCSMR;                              /*              */
        char            wk1[2];                             /*              *///FFFE9804-FFFE9800-2
        unsigned char   SCBRR;                              /* SCBRR        *///FFFE9804
        char            wk2[3];                             /*              *///FFFE9808-FFFE9804-1
        union {                                             /* SCSCR        *///FFFE9808
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short              : 8;            /*              */
                unsigned short TIE          : 1;            /*    TIE       */
                unsigned short RIE          : 1;            /*    RIE       */
                unsigned short TE           : 1;            /*    TE        */
                unsigned short RE           : 1;            /*    RE        */
                unsigned short REIE         : 1;            /*    REIE      */
                unsigned short              : 1;            /*              */
                unsigned short CKE          : 2;            /*    CKE       */
            }           BIT;                                /*              */
        }               SCSCR;                              /*              */
        char            wk3[2];                             /*              *///FFFE980C-FFFE9808-2
        unsigned char   SCFTDR;                             /* SCFTDR       *///FFFE980C
        char            wk4[3];                             /*              *///FFFE9810-FFFE980C-1
        union {                                             /* SCFSR        *///FFFE9810
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short PERC         : 4;            /*    PER3-0    */
                unsigned short FERC         : 4;            /*    FER3-0    */
                unsigned short ER           : 1;            /*    ER        */
                unsigned short TEND         : 1;            /*    TEND      */
                unsigned short TDFE         : 1;            /*    TDFE      */
                unsigned short BRK          : 1;            /*    BRK       */
                unsigned short FER          : 1;            /*    FER       */
                unsigned short PER          : 1;            /*    PER       */
                unsigned short RDF          : 1;            /*    RDF       */
                unsigned short DR           : 1;            /*    DR        */
            }           BIT;                                /*              */
        }               SCFSR;                              /*              */
        char            wk5[2];                             /*              *///FFFE9814-FFFE9810-2
        unsigned char   SCFRDR;                             /* SCFRDR       *///FFFE9814
        char            wk6[3];                             /*              *///FFFE9818-FFFE9814-1
        union {                                             /* SCFCR        *///FFFE9818
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short              : 8;            /*              */
                unsigned short RTRG         : 2;            /*    RTRG      */
                unsigned short TTRG         : 2;            /*    TTRG      */
                unsigned short              : 1;            /*              */
                unsigned short TFRST        : 1;            /*    TFRST     */
                unsigned short RFRST        : 1;            /*    RFRST     */
                unsigned short LOOP         : 1;            /*    LOOP      */
            }           BIT;                                /*              */
        }               SCFCR;                              /*              */
        char            wk7[2];                             /*              *///FFFE981C-FFFE9818-2
        union {                                             /* SCFDR        *///FFFE981C
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short              : 3;            /*              */
                unsigned short T            : 5;            /*    T         */
                unsigned short              : 3;            /*              */
                unsigned short R            : 5;            /*    R         */
            }           BIT;                                /*              */
        }               SCFDR;                              /*              */
        char            wk8[2];                             /*              *///FFFE9820-FFFE981C-2
        union {                                             /* SCSPTR       *///FFFE9820
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short              : 8;            /*              */
                unsigned short              : 4;            /*              */
                unsigned short SCKIO        : 1;            /*    SCKIO     */
                unsigned short SCKDT        : 1;            /*    SCKDT     */
                unsigned short SPB2IO       : 1;            /*    SPB2IO    */
                unsigned short SPB2DT       : 1;            /*    SPB2DT    */
            }           BIT;                                /*              */
        }               SCSPTR;                             /*              */
        char            wk9[2];                             /*              *///FFFE9824-FFFE9820-2
        union {                                             /* SCLSR        *///FFFE9824
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Accesss */
                unsigned short              :15;            /*              */
                unsigned short ORER         : 1;            /*    ORER      */
            }           BIT;                                /*              */
        }               SCLSR;                              /*              */
        char            wk10[218];                          /*              *///FFFE9900-FFFE9824-2
        union {                                             /* SCSEMR       *///FFFE9900
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char ABCS          : 1;            /*    ABCS      */
            }           BIT;                                /*              */
        }               SCSEMR;                             /*              */
};                                                          /*              */
struct st_rspi {                                            /* struct RSPI  */
        union {                                             /* SPCR         *///FFFFB000
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char SPRIE         : 1;            /*    SPRIE     */
                unsigned char SPE           : 1;            /*    SPE       */
                unsigned char SPTIE         : 1;            /*    SPTIE     */
                unsigned char SPEIE         : 1;            /*    SPEIE     */
                unsigned char MSTR          : 1;            /*    MSTR      */
                unsigned char MODFEN        : 1;            /*    MODFEN    */
                unsigned char               : 1;            /*              */
                unsigned char SPMS          : 1;            /*    SPMS      */
            }           BIT;                                /*              */
        }               SPCR;                               /*              */
        union {                                             /* SSLP         *///FFFFB0001
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 4;            /*              */
                unsigned char SSL3P         : 1;            /*    SSL3P     */
                unsigned char SSL2P         : 1;            /*    SSL2P     */
                unsigned char SSL1P         : 1;            /*    SSL1P     */
                unsigned char SSL0P         : 1;            /*    SSL0P     */
            }           BIT;                                /*              */
        }               SSLP;                               /*              */
        union {                                             /* SPPCR        *///FFFFB002
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char MOIFE         : 1;            /*    MOIFE     */
                unsigned char MOIFV         : 1;            /*    MOIFV     */
                unsigned char               : 1;            /*              */
                unsigned char SPOM          : 1;            /*    SPOM      */
                unsigned char               : 1;            /*              */
                unsigned char SPLP          : 1;            /*    SPLP      */
            }           BIT;                                /*              */
        }               SPPCR;                              /*              */
        union {                                             /* SPSR         *///FFFFB003
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char SPRF          : 1;            /*    SPRF      */
                unsigned char               : 1;            /*              */
                unsigned char SPTEF         : 1;            /*    SPTEF     */
                unsigned char               : 2;            /*              */
                unsigned char MODF          : 1;            /*    MODF      */
                unsigned char MIDLE         : 1;            /*    MIDLE     */
                unsigned char OVRF          : 1;            /*    OVRF      */
            }           BIT;                                /*              */
        }               SPSR;                               /*              */
        union {                                             /* SPDR         *///FFFFB004
            unsigned int LONG;                              /*  Long Access */
            unsigned short WORD;                            /*  Word Access */
        }               SPDR;                               /*              */
        union {                                             /* SPSCR        *///FFFFB008
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char SPSLN         : 3;            /*    SPSLN     */
            }           BIT;                                /*              */
        }               SPSCR;                              /*              */
        union {                                             /* SPSSR        *///FFFFB009
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char SPECM         : 2;            /*    SPECM     */
                unsigned char               : 2;            /*              */
                unsigned char SPCP          : 2;            /*    SPCP      */
            }           BIT;                                /*              */
        }               SPSSR;                              /*              */
        union {                                             /* SPBR         *///FFFFB00A
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char SPR           : 8;            /*    SPR       */
            }           BIT;                                /*              */
        }               SPBR;                               /*              */
        union {                                             /* SPDCR        *///FFFFB00B
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char SPLW          : 1;            /*    SPLW      */
                unsigned char SPRDTD        : 1;            /*    SPRDTD    */
                unsigned char               : 2;            /*              */
                unsigned char SPFC          : 2;            /*    SPFC      */
            }           BIT;                                /*              */
        }               SPDCR;                              /*              */
        union {                                             /* SPCKD        *///FFFFB00C
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char SCKDL         : 3;            /*    SCKDL     */
            }           BIT;                                /*              */
        }               SPCKD;                              /*              */
        union {                                             /* SSLND        *///FFFFB00D
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char SLNDL         : 3;            /*    SLNDL     */
            }           BIT;                                /*              */
        }               SSLND;                              /*              */
        union {                                             /* SPND         *///FFFFB00E
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char SPNDL         : 3;            /*    SPNDL     */
            }           BIT;                                /*              */
        }               SPND;                               /*              */
        unsigned char   wk1[1];                             /*              *///FFFFB010-FFFFB00E-1
        union {                                             /* SPCMD0       *///FFFFB010
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short SCKDEN       : 1;            /*    SCKDEN    */
                unsigned short SLNDEN       : 1;            /*    SLNDEN    */
                unsigned short SPNDEN       : 1;            /*    SPNDEN    */
                unsigned short LSBF         : 1;            /*    LSBF      */
                unsigned short SPB          : 4;            /*    SPB       */
                unsigned short SSLKP        : 1;            /*    SSLKP     */
                unsigned short SSLA         : 3;            /*    SSLA      */
                unsigned short BRDV         : 2;            /*    BRDV      */
                unsigned short CPOL         : 1;            /*    CPOL      */
                unsigned short CPHA         : 1;            /*    CPHA      */
            }           BIT;                                /*              */
        }               SPCMD0;                             /*              */
        union {                                             /* SPCMD1       *///FFFFB012
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short SCKDEN       : 1;            /*    SCKDEN    */
                unsigned short SLNDEN       : 1;            /*    SLNDEN    */
                unsigned short SPNDEN       : 1;            /*    SPNDEN    */
                unsigned short LSBF         : 1;            /*    LSBF      */
                unsigned short SPB          : 4;            /*    SPB       */
                unsigned short SSLKP        : 1;            /*    SSLKP     */
                unsigned short SSLA         : 3;            /*    SSLA      */
                unsigned short BRDV         : 2;            /*    BRDV      */
                unsigned short CPOL         : 1;            /*    CPOL      */
                unsigned short CPHA         : 1;            /*    CPHA      */
            }           BIT;                                /*              */
        }               SPCMD1;                             /*              */
        union {                                             /* SPCMD2       *///FFFFB014
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short SCKDEN       : 1;            /*    SCKDEN    */
                unsigned short SLNDEN       : 1;            /*    SLNDEN    */
                unsigned short SPNDEN       : 1;            /*    SPNDEN    */
                unsigned short LSBF         : 1;            /*    LSBF      */
                unsigned short SPB          : 4;            /*    SPB       */
                unsigned short SSLKP        : 1;            /*    SSLKP     */
                unsigned short SSLA         : 3;            /*    SSLA      */
                unsigned short BRDV         : 2;            /*    BRDV      */
                unsigned short CPOL         : 1;            /*    CPOL      */
                unsigned short CPHA         : 1;            /*    CPHA      */
            }           BIT;                                /*              */
        }               SPCMD2;                             /*              */
        union {                                             /* SPCMD3       *///FFFFB016
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short SCKDEN       : 1;            /*    SCKDEN    */
                unsigned short SLNDEN       : 1;            /*    SLNDEN    */
                unsigned short SPNDEN       : 1;            /*    SPNDEN    */
                unsigned short LSBF         : 1;            /*    LSBF      */
                unsigned short SPB          : 4;            /*    SPB       */
                unsigned short SSLKP        : 1;            /*    SSLKP     */
                unsigned short SSLA         : 3;            /*    SSLA      */
                unsigned short BRDV         : 2;            /*    BRDV      */
                unsigned short CPOL         : 1;            /*    CPOL      */
                unsigned short CPHA         : 1;            /*    CPHA      */
            }           BIT;                                /*              */
        }               SPCMD3;                             /*              */
};                                                          /*              */
struct st_iic3 {                                            /* struct IIC3  */
        union {                                             /* ICCR1        *///FFFEE000
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char ICE           : 1;            /*    ICE       */
                unsigned char RCVD          : 1;            /*    RCVD      */
                unsigned char MST           : 1;            /*    MST       */
                unsigned char TRS           : 1;            /*    TRS       */
                unsigned char CKS           : 4;            /*    CKS       */
            }           BIT;                                /*              */
        }               ICCR1;                              /*              */
        union {                                             /* ICCR2        *///FFFEE001
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char BBSY          : 1;            /*    BBSY      */
                unsigned char SCP           : 1;            /*    SCP       */
                unsigned char SDAO          : 1;            /*    SDAO      */
                unsigned char SDAOP         : 1;            /*    SDAOP     */
                unsigned char SCLO          : 1;            /*    SCLO      */
                unsigned char               : 1;            /*              */
                unsigned char IICRST        : 1;            /*  IICRST      */
            }           BIT;                                /*              */
        }               ICCR2;                              /*              */
        union {                                             /* ICMR         *///FFFEE002
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char MLS           : 1;            /*    MLS       */
                unsigned char               : 3;            /*              */
                unsigned char BCWP          : 1;            /*    BCWP      */
                unsigned char BC            : 3;            /*    BC        */
            }           BIT;                                /*              */
        }               ICMR;                               /*              */
        union {                                             /* ICIER        *///FFFEE003
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char TIE           : 1;            /*    TIE       */
                unsigned char TEIE          : 1;            /*    TEIE      */
                unsigned char RIE           : 1;            /*    RIE       */
                unsigned char NAKIE         : 1;            /*    NAKIE     */
                unsigned char STIE          : 1;            /*    STIE      */
                unsigned char ACKE          : 1;            /*    ACKE      */
                unsigned char ACKBR         : 1;            /*    ACKBR     */
                unsigned char ACKBT         : 1;            /*    ACKBT     */
            }           BIT;                                /*              */
        }               ICIER;                              /*              */
        union {                                             /* ICSR         *///FFFEE0040
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char TDRE          : 1;            /*    TDRE      */
                unsigned char TEND          : 1;            /*    TEND      */
                unsigned char RDRF          : 1;            /*    RDRF      */
                unsigned char NACKF         : 1;            /*    NACKF     */
                unsigned char STOP          : 1;            /*    STOP      */
                unsigned char ALOVE         : 1;            /*    ALOVE     */
                unsigned char AAS           : 1;            /*    AAS       */
                unsigned char ADZ           : 1;            /*    ADZ       */
            }           BIT;                                /*              */
        }               ICSR;                               /*              */
        union {                                             /* SAR          *///FFFEE005
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char SVA           : 7;            /*    SVA       */
                unsigned char FS            : 1;            /*    FS        */
            }           BIT;                                /*              */
        }               SAR;                                /*              */
        unsigned char   ICDRT;                              /* ICDRT        *///FFFEE006
        unsigned char   ICDRR;                              /* ICDRR        *///FFFEE007
        union {                                             /* NF2CYC       *///FFFEE008
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 7;            /*              */
                unsigned char NF2CYC        : 1;            /*    NF2CYC    */
            }           BIT;                                /*              */
        }               NF2CYC;                             /*              */
};                                                          /*              */
struct st_adc0 {                                            /* struct ADC0  */
        union {                                             /* ADCR         *///FFFFE800
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char ADST          : 1;            /*    ADST      */
                unsigned char ADCS          : 1;            /*    ADCS      */
                unsigned char ACE           : 1;            /*    ACE       */
                unsigned char ADIE          : 1;            /*    ADIE      */
                unsigned char               : 2;            /*              */
                unsigned char TRGE          : 1;            /*    TRGE      */
                unsigned char EXTRG         : 1;            /*    EXTRG     */
            }           BIT;                                /*              */
        }               ADCR;                               /*              */
        char            wk1[1];                             /*              *///FFFFE802-FFFFE800-1
        union {                                             /* ADSR         *///FFFFE802
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 7;            /*              */
                unsigned char ADF           : 1;            /*    ADF       */
            }           BIT;                                /*              */
        }               ADSR;                               /*              */
        char            wk2[25];                            /*              *///FFFFE81C-FFFFE802-1
        union {                                             /* ADSTRGR      *///FFFFE81C
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char STR6          : 1;            /*    STR6      */
                unsigned char STR5          : 1;            /*    STR5      */
                unsigned char STR4          : 1;            /*    STR4      */
                unsigned char STR3          : 1;            /*    STR3      */
                unsigned char STR2          : 1;            /*    STR2      */
                unsigned char STR1          : 1;            /*    STR1      */
                unsigned char STR0          : 1;            /*    STR0      */
            }           BIT;                                /*              */
        }               ADSTRGR;                            /*              */
        char            wk3[3];                             /*              *///FFFFE820-FFFFE81C-1
        union {                                             /* ADANSR       *///FFFFE820
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 4;            /*              */
                unsigned char ANS3          : 1;            /*    ANS3      */
                unsigned char ANS2          : 1;            /*    ANS2      */
                unsigned char ANS1          : 1;            /*    ANS1      */
                unsigned char ANS0          : 1;            /*    ANS0      */
            }           BIT;                                /*              */
        }               ADANSR;                             /*              */
        char            wk4[15];                            /*              *///FFFFE830-FFFFE820-1
        union {                                             /* ADBYPSCR     *///FFFFE830
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 6;            /*              */
                unsigned char               : 1;            /*              */
                unsigned char SH            : 1;            /*    SH        */
            }           BIT;                                /*              */
        }               ADBYPSCR;                           /*              */
        char            wk5[15];                            /*              *///FFFFE840-FFFFE830-1
        unsigned short  ADDR0;                              /* ADDR0        *///FFFFE840
        unsigned short  ADDR1;                              /* ADDR1        *///FFFFE842
        unsigned short  ADDR2;                              /* ADDR2        *///FFFFE844
        unsigned short  ADDR3;                              /* ADDR3        *///FFFFE846
};                                                          /*              */
struct st_adc1 {                                            /* struct ADC1  */
        union {                                             /* ADCR         *///FFFFEC00
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char ADST          : 1;            /*  ADST        */
                unsigned char ADCS          : 1;            /*  ADCS        */
                unsigned char ACE           : 1;            /*  ACE         */
                unsigned char ADIE          : 1;            /*  ADIE        */
                unsigned char               : 2;            /*              */
                unsigned char TRGE          : 1;            /*  TRGE        */
                unsigned char EXTRG         : 1;            /*  EXTRG       */
            }           BIT;                                /*              */
        }               ADCR;                               /*              */
        char            wk1;                                /*              *///FFFFEC02-FFFFEC00-1
        union {                                             /* ADSR         *///FFFFEC02
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 7;            /*              */
                unsigned char ADF           : 1;            /*  ADF         */
            }           BIT;                                /*              */
        }               ADSR;                               /*              */
        char            wk2[25];                            /*              *///FFFFEC1C-FFFFEC02-1
        union {                                             /* ADSTRGR      *///FFFFEC1C
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char STR6          : 1;            /*  STR6        */
                unsigned char STR5          : 1;            /*  STR5        */
                unsigned char STR4          : 1;            /*  STR4        */
                unsigned char STR3          : 1;            /*  STR3        */
                unsigned char STR2          : 1;            /*  STR2        */
                unsigned char STR1          : 1;            /*  STR1        */
                unsigned char STR0          : 1;            /*  STR0        */
            }           BIT;                                /*              */
        }               ADSTRGR;                            /*              */
        char            wk3[3];                             /*              *///FFFFEC20-FFFFEC1C-1
        union {                                             /* ADANSR       *///FFFFEC20
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 4;            /*              */
                unsigned char ANS3          : 1;            /*  ANS3        */
                unsigned char ANS2          : 1;            /*  ANS2        */
                unsigned char ANS1          : 1;            /*  ANS1        */
                unsigned char ANS0          : 1;            /*  ANS0        */
            }           BIT;                                /*              */
        }               ADANSR;                             /*              */
        char            wk4[15];                            /*              *///FFFFEC30-FFFFEC20-1
        union {                                             /* ADBYPSCR     *///FFFFEC30
            unsigned char BYTE;                             /*  Byte Access */
        }               ADBYPSCR;                           /*              */
        char            wk5[15];                            /*              *///FFFFEC40-FFFFEC30-1
        unsigned short  ADDR4;                              /* ADDR4        *///FFFFEC40
        unsigned short  ADDR5;                              /* ADDR5        *///FFFFEC42
        unsigned short  ADDR6;                              /* ADDR6        *///FFFFEC44
        unsigned short  ADDR7;                              /* ADDR7        *///FFFFEC46
};                                                          /*              */
struct st_rcanet {                                          /* structRCAN-ET*/
        union {                                             /* MCR          *///FFFFD000
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short IDR          : 1;            /*    IDR       */
                unsigned short AHBO         : 1;            /*    AHBO      */
                unsigned short              : 3;            /*              */
                unsigned short TST          : 3;            /*    TST       */
                unsigned short AWM          : 1;            /*    AWM       */
                unsigned short HDBO         : 1;            /*    HDBO      */
                unsigned short SLPM         : 1;            /*    SLPM      */
                unsigned short              : 2;            /*              */
                unsigned short MTP          : 1;            /*    MTP       */
                unsigned short HLTRQ        : 1;            /*    HLTRQ     */
                unsigned short RSTRQ        : 1;            /*    RSTRQ     */
            }           BIT;                                /*              */
        }               MCR;                                /*              */
        union {                                             /* GSR          *///FFFFD002
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short              :10;            /*              */
                unsigned short EPSB         : 1;            /*    EPSB      */
                unsigned short HSSB         : 1;            /*    HSSB      */
                unsigned short RSB          : 1;            /*    RSB       */
                unsigned short MTPF         : 1;            /*    MTPF      */
                unsigned short TRWF         : 1;            /*    TRWF      */
                unsigned short BOF          : 1;            /*    BOF       */
            }           BIT;                                /*              */
        }               GSR;                                /*              */
        union {                                             /* BCR1         *///FFFFD004
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short TSG1         : 4;            /*    TSG1      */
                unsigned short              : 1;            /*              */
                unsigned short TSG2         : 3;            /*    TSG2      */
                unsigned short              : 2;            /*              */
                unsigned short SJW          : 2;            /*    SJW       */
                unsigned short              : 3;            /*              */
                unsigned short BSP          : 1;            /*    BSP       */
            }           BIT;                                /*              */
        }               BCR1;                               /*              */
        union {                                             /* BCR0         *///FFFFD006
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short              : 8;            /*              */
                unsigned short BRP          : 8;            /*    BRP       */
            }           BIT;                                /*              */
        }               BCR0;                               /*              */
        union {                                             /* IRR          */
            unsigned short WORD;                            /*  Word Access *///FFFFD008
            struct {                                        /*  Bit Access  */
                unsigned short              : 2;            /*              */
                unsigned short MEIF         : 1;            /*    MEIF      */
                unsigned short BASMIF       : 1;            /*    BASMIF    */
                unsigned short              : 2;            /*              */
                unsigned short MOOIF        : 1;            /*    MOOIF     */
                unsigned short MBEIF        : 1;            /*    MBEIF     */
                unsigned short OLFIF        : 1;            /*    OLFIF     */
                unsigned short BOFIF        : 1;            /*    BOFIF     */
                unsigned short EPIF         : 1;            /*    EPIF      */
                unsigned short RECWIF       : 1;            /*    RECWIF    */
                unsigned short TECWIF       : 1;            /*    TECWIF    */
                unsigned short RFRIF        : 1;            /*    RFRIF     */
                unsigned short DFRIF        : 1;            /*    DFRIF     */
                unsigned short RSTIF        : 1;            /*    RSTIF     */
            }           BIT;                                /*              */
        }               IRR;                                /*              */
        union {                                             /* IMR          *///FFFFD00A
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short              : 2;            /*              */
                unsigned short MEIM         : 1;            /*    MEIM      */
                unsigned short BASMIM       : 1;            /*    BASMIM    */
                unsigned short              : 2;            /*              */
                unsigned short MOOIM        : 1;            /*    MOOIM     */
                unsigned short MBEIM        : 1;            /*    MBEIM     */
                unsigned short OLFIM        : 1;            /*    OLFIM     */
                unsigned short BOFIM        : 1;            /*    BOFIM     */
                unsigned short EPIM         : 1;            /*    EPIM      */
                unsigned short RECWIM       : 1;            /*    RECWIM    */
                unsigned short TECWIM       : 1;            /*    TECWIM    */
                unsigned short RFRIM        : 1;            /*    RFRIM     */
                unsigned short DFRIM        : 1;            /*    DFRIM     */
                unsigned short RSTIM        : 1;            /*    RSTIM     */
            }           BIT;                                /*              */
        }               IMR;                                /*              */
        union {                                             /* TECREC       *///FFFFD00C
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short TEC          : 8;            /*    TEC       */
                unsigned short REC          : 8;            /*    REC       */
            }           BIT;                                /*              */
        }               TECREC;                             /*              */
        char            wk1[18];                            /*              *///FFFFD020-FFFFD00C-2
        union {                                             /* TXPR1,0      *///FFFFD020
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int MB31           : 1;            /*    MB31      */
                unsigned int MB30           : 1;            /*    MB30      */
                unsigned int MB29           : 1;            /*    MB29      */
                unsigned int MB28           : 1;            /*    MB28      */
                unsigned int MB27           : 1;            /*    MB27      */
                unsigned int MB26           : 1;            /*    MB26      */
                unsigned int MB25           : 1;            /*    MB25      */
                unsigned int MB24           : 1;            /*    MB24      */
                unsigned int MB23           : 1;            /*    MB23      */
                unsigned int MB22           : 1;            /*    MB22      */
                unsigned int MB21           : 1;            /*    MB21      */
                unsigned int MB20           : 1;            /*    MB20      */
                unsigned int MB19           : 1;            /*    MB19      */
                unsigned int MB18           : 1;            /*    MB18      */
                unsigned int MB17           : 1;            /*    MB17      */
                unsigned int MB16           : 1;            /*    MB16      */
                unsigned int MB15           : 1;            /*    MB15      */
                unsigned int MB14           : 1;            /*    MB14      */
                unsigned int MB13           : 1;            /*    MB13      */
                unsigned int MB12           : 1;            /*    MB12      */
                unsigned int MB11           : 1;            /*    MB11      */
                unsigned int MB10           : 1;            /*    MB10      */
                unsigned int MB9            : 1;            /*    MB9       */
                unsigned int MB8            : 1;            /*    MB8       */
                unsigned int MB7            : 1;            /*    MB7       */
                unsigned int MB6            : 1;            /*    MB6       */
                unsigned int MB5            : 1;            /*    MB5       */
                unsigned int MB4            : 1;            /*    MB4       */
                unsigned int MB3            : 1;            /*    MB3       */
                unsigned int MB2            : 1;            /*    MB2       */
                unsigned int MB1            : 1;            /*    MB1       */
            }           BIT;                                /*              */
        }               TXPR10;                             /*              */
        char            wk2[6];                             /*              */
        union {                                             /* TXCR0        *///FFFFD02A
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short MB15         : 1;            /*    MB15      */
                unsigned short MB14         : 1;            /*    MB14      */
                unsigned short MB13         : 1;            /*    MB13      */
                unsigned short MB12         : 1;            /*    MB12      */
                unsigned short MB11         : 1;            /*    MB11      */
                unsigned short MB10         : 1;            /*    MB10      */
                unsigned short MB9          : 1;            /*    MB9       */
                unsigned short MB8          : 1;            /*    MB8       */
                unsigned short MB7          : 1;            /*    MB7       */
                unsigned short MB6          : 1;            /*    MB6       */
                unsigned short MB5          : 1;            /*    MB5       */
                unsigned short MB4          : 1;            /*    MB4       */
                unsigned short MB3          : 1;            /*    MB3       */
                unsigned short MB2          : 1;            /*    MB2       */
                unsigned short MB1          : 1;            /*    MB1       */
            }           BIT;                                /*              */
        }               TXCR0;                              /*              */
        char            wk3[6];                             /*              */
        union {                                             /* TXACK0       *///FFFFD032
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short MB15         : 1;            /*    MB15      */
                unsigned short MB14         : 1;            /*    MB14      */
                unsigned short MB13         : 1;            /*    MB13      */
                unsigned short MB12         : 1;            /*    MB12      */
                unsigned short MB11         : 1;            /*    MB11      */
                unsigned short MB10         : 1;            /*    MB10      */
                unsigned short MB9          : 1;            /*    MB9       */
                unsigned short MB8          : 1;            /*    MB8       */
                unsigned short MB7          : 1;            /*    MB7       */
                unsigned short MB6          : 1;            /*    MB6       */
                unsigned short MB5          : 1;            /*    MB5       */
                unsigned short MB4          : 1;            /*    MB4       */
                unsigned short MB3          : 1;            /*    MB3       */
                unsigned short MB2          : 1;            /*    MB2       */
                unsigned short MB1          : 1;            /*    MB1       */
            }           BIT;                                /*              */
        }               TXACK0;                             /*              */
        char            wk4[6];                             /*              */
        union {                                             /* ABACK0       *///FFFFD03A
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short MB15         : 1;            /*    MB15      */
                unsigned short MB14         : 1;            /*    MB14      */
                unsigned short MB13         : 1;            /*    MB13      */
                unsigned short MB12         : 1;            /*    MB12      */
                unsigned short MB11         : 1;            /*    MB11      */
                unsigned short MB10         : 1;            /*    MB10      */
                unsigned short MB9          : 1;            /*    MB9       */
                unsigned short MB8          : 1;            /*    MB8       */
                unsigned short MB7          : 1;            /*    MB7       */
                unsigned short MB6          : 1;            /*    MB6       */
                unsigned short MB5          : 1;            /*    MB5       */
                unsigned short MB4          : 1;            /*    MB4       */
                unsigned short MB3          : 1;            /*    MB3       */
                unsigned short MB2          : 1;            /*    MB2       */
                unsigned short MB1          : 1;            /*    MB1       */
            }           BIT;                                /*              */
        }               ABACK0;                             /*              */
        char            wk5[6];                             /*              */
        union {                                             /* RXPR0        *///FFFFD042
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short MB15         : 1;            /*    MB15      */
                unsigned short MB14         : 1;            /*    MB14      */
                unsigned short MB13         : 1;            /*    MB13      */
                unsigned short MB12         : 1;            /*    MB12      */
                unsigned short MB11         : 1;            /*    MB11      */
                unsigned short MB10         : 1;            /*    MB10      */
                unsigned short MB9          : 1;            /*    MB9       */
                unsigned short MB8          : 1;            /*    MB8       */
                unsigned short MB7          : 1;            /*    MB7       */
                unsigned short MB6          : 1;            /*    MB6       */
                unsigned short MB5          : 1;            /*    MB5       */
                unsigned short MB4          : 1;            /*    MB4       */
                unsigned short MB3          : 1;            /*    MB3       */
                unsigned short MB2          : 1;            /*    MB2       */
                unsigned short MB1          : 1;            /*    MB1       */
                unsigned short MB0          : 1;            /*    MB0       */
            }           BIT;                                /*              */
        }               RXPR0;                              /*              */
        char            wk6[6];                             /*              */
        union {                                             /* RFPR0        *///FFFFD04A
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short MB15         : 1;            /*    MB15      */
                unsigned short MB14         : 1;            /*    MB14      */
                unsigned short MB13         : 1;            /*    MB13      */
                unsigned short MB12         : 1;            /*    MB12      */
                unsigned short MB11         : 1;            /*    MB11      */
                unsigned short MB10         : 1;            /*    MB10      */
                unsigned short MB9          : 1;            /*    MB9       */
                unsigned short MB8          : 1;            /*    MB8       */
                unsigned short MB7          : 1;            /*    MB7       */
                unsigned short MB6          : 1;            /*    MB6       */
                unsigned short MB5          : 1;            /*    MB5       */
                unsigned short MB4          : 1;            /*    MB4       */
                unsigned short MB3          : 1;            /*    MB3       */
                unsigned short MB2          : 1;            /*    MB2       */
                unsigned short MB1          : 1;            /*    MB1       */
                unsigned short MB0          : 1;            /*    MB0       */
            }           BIT;                                /*              */
        }               RFPR0;                              /*              */
        char            wk7[6];                             /*              */
        union {                                             /* MBIMR0       *///FFFFD052
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short MB15         : 1;            /*    MB15      */
                unsigned short MB14         : 1;            /*    MB14      */
                unsigned short MB13         : 1;            /*    MB13      */
                unsigned short MB12         : 1;            /*    MB12      */
                unsigned short MB11         : 1;            /*    MB11      */
                unsigned short MB10         : 1;            /*    MB10      */
                unsigned short MB9          : 1;            /*    MB9       */
                unsigned short MB8          : 1;            /*    MB8       */
                unsigned short MB7          : 1;            /*    MB7       */
                unsigned short MB6          : 1;            /*    MB6       */
                unsigned short MB5          : 1;            /*    MB5       */
                unsigned short MB4          : 1;            /*    MB4       */
                unsigned short MB3          : 1;            /*    MB3       */
                unsigned short MB2          : 1;            /*    MB2       */
                unsigned short MB1          : 1;            /*    MB1       */
                unsigned short MB0          : 1;            /*    MB0       */
            }           BIT;                                /*              */
        }               MBIMR0;                             /*              */
        char            wk8[6];                             /*              */
        union {                                             /* UMSR0        *///FFFFD05A
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short MB15         : 1;            /*    MB15      */
                unsigned short MB14         : 1;            /*    MB14      */
                unsigned short MB13         : 1;            /*    MB13      */
                unsigned short MB12         : 1;            /*    MB12      */
                unsigned short MB11         : 1;            /*    MB11      */
                unsigned short MB10         : 1;            /*    MB10      */
                unsigned short MB9          : 1;            /*    MB9       */
                unsigned short MB8          : 1;            /*    MB8       */
                unsigned short MB7          : 1;            /*    MB7       */
                unsigned short MB6          : 1;            /*    MB6       */
                unsigned short MB5          : 1;            /*    MB5       */
                unsigned short MB4          : 1;            /*    MB4       */
                unsigned short MB3          : 1;            /*    MB3       */
                unsigned short MB2          : 1;            /*    MB2       */
                unsigned short MB1          : 1;            /*    MB1       */
                unsigned short MB0          : 1;            /*    MB0       */
            }           BIT;                                /*              */
        }               UMSR0;                              /*              */
        char            wk9[164];                           /*              */
        struct {                                            /* MB           */
            union {                                         /*  CTRL0       *///FFFFD100
                unsigned int LONG;                          /*   Long Access*/
                struct {                                    /*   Word Access*/
                    unsigned short H;                       /*     High     */
                    unsigned short L;                       /*     Low      */
                }       WORD;                               /*              */
                struct {                                    /*   Bit Access */
                    unsigned int IDE        : 1;            /*     IDE      */
                    unsigned int RTR        : 1;            /*     RTR      */
                    unsigned int            : 1;            /*              */
                    unsigned int STDID      :11;            /*     STDID    */
                    unsigned int EXDID      :18;            /*     EXDID    */
                }       BIT;                                /*              */
            }           CTRL0;                              /*              */
            union {                                         /*  LAFM        *///FFFFD104
                unsigned int LONG;                          /*   Long Access*/
                struct {                                    /*   Word Access*/
                    unsigned short H;                       /*     High     */
                    unsigned short L;                       /*     Low      */
                }       WORD;                               /*              */
                struct {                                    /*   Bit Access */
                    unsigned int IDE        : 1;            /*     IDE      */
                    unsigned int            : 2;            /*              */
                    unsigned int STDID      :11;            /*     STDID    */
                    unsigned int EXDID      :18;            /*     EXDID    */
                }       BIT;                                /*              */
            }           LAFM;                               /*              */
            unsigned char MSG_DATA[8];                      /*  MSG_DATA    *///FFFFD108
            union {                                         /*  CTRL1       *///FFFFD110
                unsigned short WORD;                        /*   Word Access*/
                struct {                                    /*   Byte Access*/
                    unsigned char H;                        /*     High     */
                    unsigned char L;                        /*     Low      */
                }       BYTE;                               /*              */
                struct {                                    /*   Bit Access */
                    unsigned char           : 2;            /*              */
                    unsigned char NMC       : 1;            /*     NMC      */
                    unsigned char ATX       : 1;            /*     ATX      */
                    unsigned char DART      : 1;            /*     DART     */
                    unsigned char MBC       : 3;            /*     MBC      */
                    unsigned char           : 4;            /*              */
                    unsigned char DLC       : 4;            /*     DLC      */
                }       BIT;                                /*              */
            }           CTRL1;                              /*              */
            char        wk[14];                             /*              *///FFFFD120-FFFFD110-2
        }               MB[16];                             /*              *///FFFFD120
};                                                          /*              */
struct st_pfc {                                             /* struct PFC   */
        union {                                             /* PAIORH       *///FFFE3804
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 8;            /*              */
                unsigned char               : 2;            /*              */
                unsigned char B21           : 1;            /*    Bit 21    */
                unsigned char B20           : 1;            /*    Bit 20    */
                unsigned char B19           : 1;            /*    Bit 19    */
                unsigned char B18           : 1;            /*    Bit 18    */
                unsigned char B17           : 1;            /*    Bit 17    */
                unsigned char B16           : 1;            /*    Bit 16    */
            }           BIT;                                /*              */
        }               PAIORH;                             /*              */
        union {                                             /* PAIORL       *///FFFE3806
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char B15           : 1;            /*    Bit 15    */
                unsigned char B14           : 1;            /*    Bit 14    */
                unsigned char B13           : 1;            /*    Bit 13    */
                unsigned char B12           : 1;            /*    Bit 12    */
                unsigned char B11           : 1;            /*    Bit 11    */
                unsigned char B10           : 1;            /*    Bit 10    */
                unsigned char B9            : 1;            /*    Bit 9     */
                unsigned char B8            : 1;            /*    Bit 8     */
                unsigned char B7            : 1;            /*    Bit 7     */
                unsigned char B6            : 1;            /*    Bit 6     */
                unsigned char B5            : 1;            /*    Bit 5     */
                unsigned char B4            : 1;            /*    Bit 4     */
                unsigned char B3            : 1;            /*    Bit 3     */
                unsigned char B2            : 1;            /*    Bit 2     */
                unsigned char B1            : 1;            /*    Bit 1     */
                unsigned char B0            : 1;            /*    Bit 0     */
            }           BIT;                                /*              */
        }               PAIORL;                             /*              */
        char            wk1[4];                             /*              *///FFFE380C-FFFE3806-2
        union {                                             /* PACRH2       *///FFFE380C
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char               : 3;            /*              */
                unsigned char               : 1;            /*              */
                unsigned char               : 3;            /*              */
                unsigned char               : 1;            /*              */
                unsigned char PA21MD        : 3;            /*    PA21MD    */
                unsigned char               : 1;            /*              */
                unsigned char PA20MD        : 3;            /*    PA20MD    */
            }           BIT;                                /*              */
        }               PACRH2;                             /*              */
        union {                                             /* PACRH1       *///FFFE380E
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PA19MD        : 3;            /*    PA19MD    */
                unsigned char               : 1;            /*              */
                unsigned char PA18MD        : 3;            /*    PA18MD    */
                unsigned char               : 1;            /*              */
                unsigned char PA17MD        : 3;            /*    PA17MD    */
                unsigned char               : 1;            /*              */
                unsigned char PA16MD        : 3;            /*    PA16MD    */
            }           BIT;                                /*              */
        }               PACRH1;                             /*              */
        union {                                             /* PACRL4       *///FFFE3810
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PA15MD        : 3;            /*    PA15MD    */
                unsigned char               : 1;            /*              */
                unsigned char PA14MD        : 3;            /*    PA14MD    */
                unsigned char               : 1;            /*              */
                unsigned char PA13MD        : 3;            /*    PA13MD    */
                unsigned char               : 1;            /*              */
                unsigned char PA12MD        : 3;            /*    PA12MD    */
            }           BIT;                                /*              */
        }               PACRL4;                             /*              */
        union {                                             /* PACRL3       *///FFFE3812
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PA11MD        : 3;            /*    PA11MD    */
                unsigned char               : 1;            /*              */
                unsigned char PA10MD        : 3;            /*    PA10MD    */
                unsigned char               : 1;            /*              */
                unsigned char PA9MD         : 3;            /*    PA9MD     */
                unsigned char               : 1;            /*              */
                unsigned char PA8MD         : 3;            /*    PA8MD     */
            }           BIT;                                /*              */
        }               PACRL3;                             /*              */
        union {                                             /* PACRL2       *///FFFE3814
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PA7MD         : 3;            /*    PA7MD     */
                unsigned char               : 1;            /*              */
                unsigned char PA6MD         : 3;            /*    PA6MD     */
                unsigned char               : 1;            /*              */
                unsigned char PA5MD         : 3;            /*    PA5MD     */
                unsigned char               : 1;            /*              */
                unsigned char PA4MD         : 3;            /*    PA4MD     */
            }           BIT;                                /*              */
        }               PACRL2;                             /*              */
        union {                                             /* PACRL1       *///FFFE3816
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PA3MD         : 3;            /*    PA3MD     */
                unsigned char               : 1;            /*              */
                unsigned char PA2MD         : 3;            /*    PA2MD     */
                unsigned char               : 1;            /*              */
                unsigned char PA1MD         : 3;            /*    PA1MD     */
                unsigned char               : 1;            /*              */
                unsigned char PA0MD         : 3;            /*    PA0MD     */
            }           BIT;                                /*              */
        }               PACRL1;                             /*              */
        char            wk2[16];                            /*              *///FFFE3828-FFFE3810-8
        union {                                             /* PAPCRH       *///FFFE3828
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 8;            /*              */
                unsigned char               : 2;            /*              */
                unsigned char PA21PCR       : 1;            /*    PA21PCR   */
                unsigned char PA20PCR       : 1;            /*    PA20PCR   */
                unsigned char PA19PCR       : 1;            /*    PA19PCR   */
                unsigned char PA18PCR       : 1;            /*    PA18PCR   */
                unsigned char PA17PCR       : 1;            /*    PA17PCR   */
                unsigned char PA16PCR       : 1;            /*    PA16PCR   */
            }           BIT;                                /*              */
        }               PAPCRH;                             /*              */
        union {                                             /* PAPCRL       *///FFFE382A
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char PA15PCR       : 1;            /*    PA15PCR   */
                unsigned char PA14PCR       : 1;            /*    PA14PCR   */
                unsigned char PA13PCR       : 1;            /*    PA13PCR   */
                unsigned char PA12PCR       : 1;            /*    PA12PCR   */
                unsigned char PA11PCR       : 1;            /*    PA11PCR   */
                unsigned char PA10PCR       : 1;            /*    PA10PCR   */
                unsigned char PA9PCR        : 1;            /*    PA9PCR    */
                unsigned char PA8PCR        : 1;            /*    PA8PCR    */
                unsigned char PA7PCR        : 1;            /*    PA7PCR    */
                unsigned char PA6PCR        : 1;            /*    PA6PCR    */
                unsigned char PA5PCR        : 1;            /*    PA5PCR    */
                unsigned char PA4PCR        : 1;            /*    PA4PCR    */
                unsigned char PA3PCR        : 1;            /*    PA3PCR    */
                unsigned char PA2PCR        : 1;            /*    PA2PCR    */
                unsigned char PA1PCR        : 1;            /*    PA1PCR    */
                unsigned char PA0PCR        : 1;            /*    PA0PCR    */
            }           BIT;                                /*              */
        }               PAPCRL;                             /*              */
        char            wk3[90];                            /*              *///FFFE3886-FFFE3828-4
        union {                                             /* PBIORL       *///FFFE3886
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char B15           : 1;            /*    Bit 15    */
                unsigned char B14           : 1;            /*    Bit 14    */
                unsigned char B13           : 1;            /*    Bit 13    */
                unsigned char B12           : 1;            /*    Bit 12    */
                unsigned char B11           : 1;            /*    Bit 11    */
                unsigned char B10           : 1;            /*    Bit 10    */
                unsigned char B9            : 1;            /*    Bit 9     */
                unsigned char B8            : 1;            /*    Bit 8     */
                unsigned char B7            : 1;            /*    Bit 7     */
                unsigned char B6            : 1;            /*    Bit 6     */
                unsigned char B5            : 1;            /*    Bit 5     */
                unsigned char B4            : 1;            /*    Bit 4     */
                unsigned char B3            : 1;            /*    Bit 3     */
                unsigned char B2            : 1;            /*    Bit 2     */
                unsigned char B1            : 1;            /*    Bit 1     */
                unsigned char B0            : 1;            /*    Bit 0     */
            }           BIT;                                /*              */
        }               PBIORL;                             /*              */
        char            wk4[8];                             /*              *///FFFE3890-FFFE3884-4
        union {                                             /* PBCRL4       *///FFFE3890
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PB15MD        : 3;            /*    PB15MD    */
                unsigned char               : 1;            /*              */
                unsigned char PB14MD        : 3;            /*    PB14MD    */
                unsigned char               : 1;            /*              */
                unsigned char PB13MD        : 3;            /*    PB13MD    */
                unsigned char               : 1;            /*              */
                unsigned char PB12MD        : 3;            /*    PB12MD    */
            }           BIT;                                /*              */
        }               PBCRL4;                             /*              */
        union {                                             /* PBCRL3       *///FFFE3892
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PB11MD        : 3;            /*    PB11MD    */
                unsigned char               : 1;            /*              */
                unsigned char PB10MD        : 3;            /*    PB10MD    */
                unsigned char               : 1;            /*              */
                unsigned char PB9MD         : 3;            /*    PB9MD     */
                unsigned char               : 1;            /*              */
                unsigned char PB8MD         : 3;            /*    PB8MD     */
            }           BIT;                                /*              */
        }               PBCRL3;                             /*              */
        union {                                             /* PBCRL2       *///FFFE3894
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PB7MD         : 3;            /*    PB7MD     */
                unsigned char               : 1;            /*              */
                unsigned char PB6MD         : 3;            /*    PB6MD     */
                unsigned char               : 1;            /*              */
                unsigned char PB5MD         : 3;            /*    PB5MD     */
                unsigned char               : 1;            /*              */
                unsigned char PB4MD         : 3;            /*    PB4MD     */
            }           BIT;                                /*              */
        }               PBCRL2;                             /*              */
        union {                                             /* PBCRL1       *///FFFE3896
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PB3MD         : 3;            /*    PB3MD     */
                unsigned char               : 1;            /*              */
                unsigned char PB2MD         : 3;            /*    PB2MD     */
                unsigned char               : 1;            /*              */
                unsigned char PB1MD         : 3;            /*    PB1MD     */
                unsigned char               : 1;            /*              */
                unsigned char PB0MD         : 3;            /*    PB0MD     */
            }           BIT;                                /*              */
        }               PBCRL1;                             /*              */
        char            wk5[18];                            /*              *///FFFE38AA-FFFE3896-2
        union {                                             /* PBPCRL       *///FFFE38AA
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char PB15PCR       : 1;            /*    PB15PCR   */
                unsigned char PB14PCR       : 1;            /*    PB14PCR   */
                unsigned char PB13PCR       : 1;            /*    PB13PCR   */
                unsigned char PB12PCR       : 1;            /*    PB12PCR   */
                unsigned char PB11PCR       : 1;            /*    PB11PCR   */
                unsigned char PB10PCR       : 1;            /*    PB10PCR   */
                unsigned char PB9PCR        : 1;            /*    PB9PCR    */
                unsigned char PB8PCR        : 1;            /*    PB8PCR    */
                unsigned char PB7PCR        : 1;            /*    PB7PCR    */
                unsigned char PB6PCR        : 1;            /*    PB6PCR    */
                unsigned char PB5PCR        : 1;            /*    PB5PCR    */
                unsigned char PB4PCR        : 1;            /*    PB4PCR    */
                unsigned char PB3PCR        : 1;            /*    PB3PCR    */
                unsigned char PB2PCR        : 1;            /*    PB2PCR    */
                unsigned char PB1PCR        : 1;            /*    PB1PCR    */
                unsigned char PB0PCR        : 1;            /*    PB0PCR    */
            }           BIT;                                /*              */
        }               PBPCRL;                             /*              */
        char            wk6[90];                            /*              *///FFFE3906-FFFE38A8-4
        union {                                             /* PCIORL       *///FFFE3906
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char B15           : 1;            /*    Bit 15    */
                unsigned char B14           : 1;            /*    Bit 14    */
                unsigned char B13           : 1;            /*    Bit 13    */
                unsigned char B12           : 1;            /*    Bit 12    */
                unsigned char B11           : 1;            /*    Bit 11    */
                unsigned char B10           : 1;            /*    Bit 10    */
                unsigned char B9            : 1;            /*    Bit 9     */
                unsigned char B8            : 1;            /*    Bit 8     */
                unsigned char B7            : 1;            /*    Bit 7     */
                unsigned char B6            : 1;            /*    Bit 6     */
                unsigned char B5            : 1;            /*    Bit 5     */
                unsigned char B4            : 1;            /*    Bit 4     */
                unsigned char B3            : 1;            /*    Bit 3     */
                unsigned char B2            : 1;            /*    Bit 2     */
                unsigned char B1            : 1;            /*    Bit 1     */
                unsigned char B0            : 1;            /*    Bit 0     */
            }           BIT;                                /*              */
        }               PCIORL;                             /*              */
        char            wk7[8];                             /*              *///FFFE3910-FFFE3906-2
        union {                                             /* PCCRL4       *///FFFE3910
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PC15MD        : 3;            /*    PC15MD    */
                unsigned char               : 1;            /*              */
                unsigned char PC14MD        : 3;            /*    PC14MD    */
                unsigned char               : 1;            /*              */
                unsigned char PC13MD        : 3;            /*    PC13MD    */
                unsigned char               : 1;            /*              */
                unsigned char PC12MD        : 3;            /*    PC12MD    */
            }           BIT;                                /*              */
        }               PCCRL4;                             /*              */
        union {                                             /* PCCRL3       *///FFFE3912
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PC11MD        : 3;            /*    PC11MD    */
                unsigned char               : 1;            /*              */
                unsigned char PC10MD        : 3;            /*    PC10MD    */
                unsigned char               : 1;            /*              */
                unsigned char PC9MD         : 3;            /*    PC9MD     */
                unsigned char               : 1;            /*              */
                unsigned char PC8MD         : 3;            /*    PC8MD     */
            }           BIT;                                /*              */
        }               PCCRL3;                             /*              */
        union {                                             /* PCCRL2       *///FFFE3914
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PC7MD         : 3;            /*    PC7MD     */
                unsigned char               : 1;            /*              */
                unsigned char PC6MD         : 3;            /*    PC6MD     */
                unsigned char               : 1;            /*              */
                unsigned char PC5MD         : 3;            /*    PC5MD     */
                unsigned char               : 1;            /*              */
                unsigned char PC4MD         : 3;            /*    PC4MD     */
            }           BIT;                                /*              */
        }               PCCRL2;                             /*              */
        union {                                             /* PCCRL1       *///FFFE3916
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PC3MD         : 3;            /*    PC3MD     */
                unsigned char               : 1;            /*              */
                unsigned char PC2MD         : 3;            /*    PC2MD     */
                unsigned char               : 1;            /*              */
                unsigned char PC1MD         : 3;            /*    PC1MD     */
                unsigned char               : 1;            /*              */
                unsigned char PC0MD         : 3;            /*    PC0MD     */
            }           BIT;                                /*              */
        }               PCCRL1;                             /*              */
        char            wk8[18];                            /*              *///FFFE392A-FFFE3916-2
        union {                                             /* PCPCRL       *///FFFE392A
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char PC15PCR       : 1;            /*    PC15PCR   */
                unsigned char PC14PCR       : 1;            /*    PC14PCR   */
                unsigned char PC13PCR       : 1;            /*    PC13PCR   */
                unsigned char PC12PCR       : 1;            /*    PC12PCR   */
                unsigned char PC11PCR       : 1;            /*    PC11PCR   */
                unsigned char PC10PCR       : 1;            /*    PC10PCR   */
                unsigned char PC9PCR        : 1;            /*    PC9PCR    */
                unsigned char PC8PCR        : 1;            /*    PC8PCR    */
                unsigned char PC7PCR        : 1;            /*    PC7PCR    */
                unsigned char PC6PCR        : 1;            /*    PC6PCR    */
                unsigned char PC5PCR        : 1;            /*    PC2PCR    */
                unsigned char PC4PCR        : 1;            /*    PC1PCR    */
                unsigned char PC3PCR        : 1;            /*    PC0PCR    */
                unsigned char PC2PCR        : 1;            /*    PC2PCR    */
                unsigned char PC1PCR        : 1;            /*    PC1PCR    */
                unsigned char PC0PCR        : 1;            /*    PC0PCR    */
            }           BIT;                                /*              */
        }               PCPCRL;                             /*              */
        char            wk9[88];                            /*              *///FFFE3984-FFFE392A-2
        union {                                             /* PDIORH       *///FFFE3984
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char B31           : 1;            /*    Bit 31    */
                unsigned char B30           : 1;            /*    Bit 30    */
                unsigned char B29           : 1;            /*    Bit 29    */
                unsigned char B28           : 1;            /*    Bit 28    */
                unsigned char B27           : 1;            /*    Bit 27    */
                unsigned char B26           : 1;            /*    Bit 26    */
                unsigned char B25           : 1;            /*    Bit 25    */
                unsigned char B24           : 1;            /*    Bit 24    */
                unsigned char B23           : 1;            /*    Bit 23    */
                unsigned char B22           : 1;            /*    Bit 22    */
                unsigned char B21           : 1;            /*    Bit 21    */
                unsigned char B20           : 1;            /*    Bit 20    */
                unsigned char B19           : 1;            /*    Bit 19    */
                unsigned char B18           : 1;            /*    Bit 18    */
                unsigned char B17           : 1;            /*    Bit 17    */
                unsigned char B16           : 1;            /*    Bit 16    */
            }           BIT;                                /*              */
        }               PDIORH;                             /*              */
        union {                                             /* PDIORL       *///FFFE3986
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char B15           : 1;            /*    Bit 15    */
                unsigned char B14           : 1;            /*    Bit 14    */
                unsigned char B13           : 1;            /*    Bit 13    */
                unsigned char B12           : 1;            /*    Bit 12    */
                unsigned char B11           : 1;            /*    Bit 11    */
                unsigned char B10           : 1;            /*    Bit 10    */
                unsigned char B9            : 1;            /*    Bit 9     */
                unsigned char B8            : 1;            /*    Bit 8     */
                unsigned char B7            : 1;            /*    Bit 7     */
                unsigned char B6            : 1;            /*    Bit 6     */
                unsigned char B5            : 1;            /*    Bit 5     */
                unsigned char B4            : 1;            /*    Bit 4     */
                unsigned char B3            : 1;            /*    Bit 3     */
                unsigned char B2            : 1;            /*    Bit 2     */
                unsigned char B1            : 1;            /*    Bit 1     */
                unsigned char B0            : 1;            /*    Bit 0     */
            }           BIT;                                /*              */
        }               PDIORL;                             /*              */
        union {                                             /* PDCRH4       *///FFFE3988
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PD31MD        : 3;            /*    PD31MD    */
                unsigned char               : 1;            /*              */
                unsigned char PD30MD        : 3;            /*    PD30MD    */
                unsigned char               : 1;            /*              */
                unsigned char PD29MD        : 3;            /*    PD29MD    */
                unsigned char               : 1;            /*              */
                unsigned char PD28MD        : 3;            /*    PD28MD    */
            }           BIT;                                /*              */
        }               PDCRH4;                             /*              */
        union {                                             /* PDCRH3       *///FFFE398A
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PD27MD        : 3;            /*    PD27MD    */
                unsigned char               : 1;            /*              */
                unsigned char PD26MD        : 3;            /*    PD26MD    */
                unsigned char               : 1;            /*              */
                unsigned char PD25MD        : 3;            /*    PD25MD    */
                unsigned char               : 1;            /*              */
                unsigned char PD24MD        : 3;            /*    PD24MD    */
            }           BIT;                                /*              */
        }               PDCRH3;                             /*              */
        union {                                             /* PDCRH2       *///FFFE398C
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PD23MD        : 3;            /*    PD23MD    */
                unsigned char               : 1;            /*              */
                unsigned char PD22MD        : 3;            /*    PD22MD    */
                unsigned char               : 1;            /*              */
                unsigned char PD21MD        : 3;            /*    PD21MD    */
                unsigned char               : 1;            /*              */
                unsigned char PD20MD        : 3;            /*    PD20MD    */
            }           BIT;                                /*              */
        }               PDCRH2;                             /*              */
        union {                                             /* PDCRH1       *///FFFE398E
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PD19MD        : 3;            /*    PD19MD    */
                unsigned char               : 1;            /*              */
                unsigned char PD18MD        : 3;            /*    PD18MD    */
                unsigned char               : 1;            /*              */
                unsigned char PD17MD        : 3;            /*    PD17MD    */
                unsigned char               : 1;            /*              */
                unsigned char PD16MD        : 3;            /*    PD16MD    */
            }           BIT;                                /*              */
        }               PDCRH1;                             /*              */
        union {                                             /* PDCRL4       *///FFFE3990
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PD15MD        : 3;            /*    PD15MD    */
                unsigned char               : 1;            /*              */
                unsigned char PD14MD        : 3;            /*    PD14MD    */
                unsigned char               : 1;            /*              */
                unsigned char PD13MD        : 3;            /*    PD13MD    */
                unsigned char               : 1;            /*              */
                unsigned char PD12MD        : 3;            /*    PD12MD    */
            }           BIT;                                /*              */
        }               PDCRL4;                             /*              */
        union {                                             /* PDCRL3       *///FFFE3992
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PD11MD        : 3;            /*    PD11MD    */
                unsigned char               : 1;            /*              */
                unsigned char PD10MD        : 3;            /*    PD10MD    */
                unsigned char               : 1;            /*              */
                unsigned char PD9MD         : 3;            /*    PD9MD     */
                unsigned char               : 1;            /*              */
                unsigned char PD8MD         : 3;            /*    PD8MD     */
            }           BIT;                                /*              */
        }               PDCRL3;                             /*              */
        union {                                             /* PDCRL2       *///FFFE3994
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PD7MD         : 3;            /*    PD7MD     */
                unsigned char               : 1;            /*              */
                unsigned char PD6MD         : 3;            /*    PD6MD     */
                unsigned char               : 1;            /*              */
                unsigned char PD5MD         : 3;            /*    PD5MD     */
                unsigned char               : 1;            /*              */
                unsigned char PD4MD         : 3;            /*    PD4MD     */
            }           BIT;                                /*              */
        }               PDCRL2;                             /*              */
        union {                                             /* PDCRL1       *///FFFE3996
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PD3MD         : 3;            /*    PD3MD     */
                unsigned char               : 1;            /*              */
                unsigned char PD2MD         : 3;            /*    PD2MD     */
                unsigned char               : 1;            /*              */
                unsigned char PD1MD         : 3;            /*    PD1MD     */
                unsigned char               : 1;            /*              */
                unsigned char PD0MD         : 3;            /*    PD0MD     */
            }           BIT;                                /*              */
        }               PDCRL1;                             /*              */
        char            wk10[16];                           /*              *///FFFE39A8-FFFE3996-2
        union {                                             /* PDPCRH       *///FFFE39A8
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char PD31PCR       : 1;            /*    PD31PCR   */
                unsigned char PD30PCR       : 1;            /*    PD30PCR   */
                unsigned char PD29PCR       : 1;            /*    PD29PCR   */
                unsigned char PD28PCR       : 1;            /*    PD28PCR   */
                unsigned char PD27PCR       : 1;            /*    PD27PCR   */
                unsigned char PD26PCR       : 1;            /*    PD26PCR   */
                unsigned char PD25PCR       : 1;            /*    PD25PCR   */
                unsigned char PD24PCR       : 1;            /*    PD24PCR   */
                unsigned char PD23PCR       : 1;            /*    PD23PCR   */
                unsigned char PD22PCR       : 1;            /*    PD22PCR   */
                unsigned char PD21PCR       : 1;            /*    PD21PCR   */
                unsigned char PD20PCR       : 1;            /*    PD20PCR   */
                unsigned char PD19PCR       : 1;            /*    PD19PCR   */
                unsigned char PD18PCR       : 1;            /*    PD18PCR   */
                unsigned char PD17PCR       : 1;            /*    PD17PCR   */
                unsigned char PD16PCR       : 1;            /*    PD16PCR   */
            }           BIT;                                /*              */
        }               PDPCRH;                             /*              */
        union {                                             /* PDPCRL       *///FFFE39AA
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char PD15PCR       : 1;            /*    PD15PCR   */
                unsigned char PD14PCR       : 1;            /*    PD14PCR   */
                unsigned char PD13PCR       : 1;            /*    PD13PCR   */
                unsigned char PD12PCR       : 1;            /*    PD12PCR   */
                unsigned char PD11PCR       : 1;            /*    PD11PCR   */
                unsigned char PD10PCR       : 1;            /*    PD10PCR   */
                unsigned char PD9PCR        : 1;            /*    PD9PCR    */
                unsigned char PD8PCR        : 1;            /*    PD8PCR    */
                unsigned char PD7PCR        : 1;            /*    PD7PCR    */
                unsigned char PD6PCR        : 1;            /*    PD6PCR    */
                unsigned char PD5PCR        : 1;            /*    PD5PCR    */
                unsigned char PD4PCR        : 1;            /*    PD4PCR    */
                unsigned char PD3PCR        : 1;            /*    PD3PCR    */
                unsigned char PD2PCR        : 1;            /*    PD2PCR    */
                unsigned char PD1PCR        : 1;            /*    PD1PCR    */
                unsigned char PD0PCR        : 1;            /*    PD0PCR    */
            }           BIT;                                /*              */
        }               PDPCRL;                             /*              */
        char            wk11[90];                           /*              *///FFFE3A06-FFFE39AA-2
        union {                                             /* PEIORL       *///FFFE3A06
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char B15           : 1;            /*    Bit 15    */
                unsigned char B14           : 1;            /*    Bit 14    */
                unsigned char B13           : 1;            /*    Bit 13    */
                unsigned char B12           : 1;            /*    Bit 12    */
                unsigned char B11           : 1;            /*    Bit 11    */
                unsigned char B10           : 1;            /*    Bit 10    */
                unsigned char B9            : 1;            /*    Bit 9     */
                unsigned char B8            : 1;            /*    Bit 8     */
                unsigned char B7            : 1;            /*    Bit 7     */
                unsigned char B6            : 1;            /*    Bit 6     */
                unsigned char B5            : 1;            /*    Bit 5     */
                unsigned char B4            : 1;            /*    Bit 4     */
                unsigned char B3            : 1;            /*    Bit 3     */
                unsigned char B2            : 1;            /*    Bit 2     */
                unsigned char B1            : 1;            /*    Bit 1     */
                unsigned char B0            : 1;            /*    Bit 0     */
            }           BIT;                                /*              */
        }               PEIORL;                             /*              */
        char            wk12[8];                            /*              *///FFFE3A10-FFFE3A06-2
        union {                                             /* PECRL4       *///FFFE3A10
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PE15MD        : 3;            /*    PE15MD    */
                unsigned char               : 1;            /*              */
                unsigned char PE14MD        : 3;            /*    PE14MD    */
                unsigned char               : 1;            /*              */
                unsigned char PE13MD        : 3;            /*    PE13MD    */
                unsigned char               : 1;            /*              */
                unsigned char PE12MD        : 3;            /*    PE12MD    */
            }           BIT;                                /*              */
        }               PECRL4;                             /*              */
        union {                                             /* PECRL3       *///FFFE3A12
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PE11MD        : 3;            /*    PE11MD    */
                unsigned char               : 1;            /*              */
                unsigned char PE10MD        : 3;            /*    PE10MD    */
                unsigned char               : 1;            /*              */
                unsigned char PE9MD         : 3;            /*    PE9MD     */
                unsigned char               : 1;            /*              */
                unsigned char PE8MD         : 3;            /*    PE8MD     */
            }           BIT;                                /*              */
        }               PECRL3;                             /*              */
        union {                                             /* PECRL2       *///FFFE3A14
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PE7MD         : 3;            /*    PE7MD     */
                unsigned char               : 1;            /*              */
                unsigned char PE6MD         : 3;            /*    PE6MD     */
                unsigned char               : 1;            /*              */
                unsigned char PE5MD         : 3;            /*    PE5MD     */
                unsigned char               : 1;            /*              */
                unsigned char PE4MD         : 3;            /*    PE4MD     */
            }           BIT;                                /*              */
        }               PECRL2;                             /*              */
        union {                                             /* PECRL1       *///FFFE3A16
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char PE3MD         : 3;            /*    PE3MD     */
                unsigned char               : 1;            /*              */
                unsigned char PE2MD         : 3;            /*    PE2MD     */
                unsigned char               : 1;            /*              */
                unsigned char PE1MD         : 3;            /*    PE1MD     */
                unsigned char               : 1;            /*              */
                unsigned char PE0MD         : 3;            /*    PE0MD     */
            }           BIT;                                /*              */
        }               PECRL1;                             /*              */
        char            wk13[8];                            /*              *///FFFE3A20-FFFE3A16-2
        union {                                             /* HCPCR        *///FFFE3A20
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 8;            /*              */
                unsigned char               : 4;            /*              */
                unsigned char MZIZDH        : 1;            /*    MZIZDH    */
                unsigned char MZIZDL        : 1;            /*    MZIZDL    */
                unsigned char MZIZEH        : 1;            /*    MZIZEH    */
                unsigned char MZIZEL        : 1;            /*    MZIZEL    */
            }           BIT;                                /*              */
            }           HCPCR;                              /*              */
        union {                                             /* IFCR         *///FFFE3A22
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 8;            /*              */
                unsigned char               : 4;            /*              */
                unsigned char IRQMD32       : 2;            /*    IRQMD3/2  */
                unsigned char IRQMD10       : 2;            /*    IRQMD1/0  */
            }           BIT;                                /*              */
        }               IFCR;                               /*              */
        char            wk14[6];                            /*              *///FFFE3A2A-FFFE3A22-2
        union {                                             /* PEPCRL       *///FFFE3A2A
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char PE15PCR       : 1;            /*    PE15PCR   */
                unsigned char PE14PCR       : 1;            /*    PE14PCR   */
                unsigned char PE13PCR       : 1;            /*    PE13PCR   */
                unsigned char PE12PCR       : 1;            /*    PE12PCR   */
                unsigned char PE11PCR       : 1;            /*    PE11PCR   */
                unsigned char PE10PCR       : 1;            /*    PE10PCR   */
                unsigned char PE9PCR        : 1;            /*    PE9PCR    */
                unsigned char PE8PCR        : 1;            /*    PE8PCR    */
                unsigned char PE7PCR        : 1;            /*    PE7PCR    */
                unsigned char PE6PCR        : 1;            /*    PE6PCR    */
                unsigned char PE5PCR        : 1;            /*    PE5PCR    */
                unsigned char PE4PCR        : 1;            /*    PE4PCR    */
                unsigned char PE3PCR        : 1;            /*    PE3PCR    */
                unsigned char PE2PCR        : 1;            /*    PE2PCR    */
                unsigned char PE1PCR        : 1;            /*    PE1PCR    */
                unsigned char PE0PCR        : 1;            /*    PE0PCR    */
            }           BIT;                                /*              */
        }               PEPCRL;                             /*              */
        union {                                             /* PDACKCR      *///FFFE3A2C
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 8;            /*              */
                unsigned char               : 4;            /*              */
                unsigned char DACK3TMG      : 1;            /*    DACK3TMG  */
                unsigned char DACK2TMG      : 1;            /*    DACK2TMG  */
                unsigned char DACK1TMG      : 1;            /*    DACK1TMG  */
                unsigned char DACK0TMG      : 1;            /*    DACK0TMG  */
            }           BIT;                                /*              */
        }               PDACKCR;                            /*              */
};                                                          /*              */
struct st_pa {                                              /* struct PA    */
        union {                                             /* PADR         *///FFFE3800
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Word Access */
                unsigned short H;                           /*    High      */
                unsigned short L;                           /*    Low       */
            }           WORD;                               /*              */
            struct {                                        /*  Byte Access */
                unsigned char HH;                           /*    High,High */
                unsigned char HL;                           /*    High,Low  */
                unsigned char LH;                           /*    Low,High  */
                unsigned char LL;                           /*    Low,Low   */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 8;            /*              */
                unsigned char               : 2;            /*              */
                unsigned char B21           : 1;            /*    Bit 21    */
                unsigned char B20           : 1;            /*    Bit 20    */
                unsigned char B19           : 1;            /*    Bit 19    */
                unsigned char B18           : 1;            /*    Bit 18    */
                unsigned char B17           : 1;            /*    Bit 17    */
                unsigned char B16           : 1;            /*    Bit 16    */
                unsigned char B15           : 1;            /*    Bit 15    */
                unsigned char B14           : 1;            /*    Bit 14    */
                unsigned char B13           : 1;            /*    Bit 13    */
                unsigned char B12           : 1;            /*    Bit 12    */
                unsigned char B11           : 1;            /*    Bit 11    */
                unsigned char B10           : 1;            /*    Bit 10    */
                unsigned char B9            : 1;            /*    Bit 9     */
                unsigned char B8            : 1;            /*    Bit 8     */
                unsigned char B7            : 1;            /*    Bit 7     */
                unsigned char B6            : 1;            /*    Bit 6     */
                unsigned char B5            : 1;            /*    Bit 5     */
                unsigned char B4            : 1;            /*    Bit 4     */
                unsigned char B3            : 1;            /*    Bit 3     */
                unsigned char B2            : 1;            /*    Bit 2     */
                unsigned char B1            : 1;            /*    Bit 1     */
                unsigned char B0            : 1;            /*    Bit 0     */
            }           BIT;                                /*              */
        }               DR;                                 /*              */
        char            wk1[24];                            /*              *///FFFE381C-FFFEE3800-4
        union {                                             /* PAPR         *///FFFE381C
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Word Access */
                unsigned short H;                           /*    High      */
                unsigned short L;                           /*    Low       */
            }           WORD;                               /*              */
            struct {                                        /*  Byte Access */
                unsigned char HH;                           /*    High,High */
                unsigned char HL;                           /*    High,Low  */
                unsigned char LH;                           /*    Low,High  */
                unsigned char LL;                           /*    Low,Low   */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 8;            /*              */
                unsigned char               : 2;            /*              */
                unsigned char B21           : 1;            /*    Bit 21    */
                unsigned char B20           : 1;            /*    Bit 20    */
                unsigned char B19           : 1;            /*    Bit 19    */
                unsigned char B18           : 1;            /*    Bit 18    */
                unsigned char B17           : 1;            /*    Bit 17    */
                unsigned char B16           : 1;            /*    Bit 16    */
                unsigned char B15           : 1;            /*    Bit 15    */
                unsigned char B14           : 1;            /*    Bit 14    */
                unsigned char B13           : 1;            /*    Bit 13    */
                unsigned char B12           : 1;            /*    Bit 12    */
                unsigned char B11           : 1;            /*    Bit 11    */
                unsigned char B10           : 1;            /*    Bit 10    */
                unsigned char B9            : 1;            /*    Bit 9     */
                unsigned char B8            : 1;            /*    Bit 8     */
                unsigned char B7            : 1;            /*    Bit 7     */
                unsigned char B6            : 1;            /*    Bit 6     */
                unsigned char B5            : 1;            /*    Bit 5     */
                unsigned char B4            : 1;            /*    Bit 4     */
                unsigned char B3            : 1;            /*    Bit 3     */
                unsigned char B2            : 1;            /*    Bit 2     */
                unsigned char B1            : 1;            /*    Bit 1     */
                unsigned char B0            : 1;            /*    Bit 0     */
            }           BIT;                                /*              */
        }               PR;                                 /*              */
};                                                          /*              */
struct st_pb {                                              /* struct PB    */
        char            wk1[2];                             /*              *///FFFE3800
        union {                                             /* PBDR         *///FFFE3882
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char B15           : 1;            /*    Bit 15    */
                unsigned char B14           : 1;            /*    Bit 14    */
                unsigned char B13           : 1;            /*    Bit 13    */
                unsigned char B12           : 1;            /*    Bit 12    */
                unsigned char B11           : 1;            /*    Bit 11    */
                unsigned char B10           : 1;            /*    Bit 10    */
                unsigned char B9            : 1;            /*    Bit 9     */
                unsigned char B8            : 1;            /*    Bit 8     */
                unsigned char B7            : 1;            /*    Bit 7     */
                unsigned char B6            : 1;            /*    Bit 6     */
                unsigned char B5            : 1;            /*    Bit 5     */
                unsigned char B4            : 1;            /*    Bit 4     */
                unsigned char B3            : 1;            /*    Bit 3     */
                unsigned char B2            : 1;            /*    Bit 2     */
                unsigned char B1            : 1;            /*    Bit 1     */
                unsigned char B0            : 1;            /*    Bit 0     */
            }           BIT;                                /*              */
        }               DR;                                 /*              */
        char            wk2[26];                            /*              *///FFFE389E-FFFE3882-2
        union {                                             /* PBPR         *///FFFE389E
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    High      */
                }       BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char B15           : 1;            /*    Bit 15    */
                unsigned char B14           : 1;            /*    Bit 14    */
                unsigned char B13           : 1;            /*    Bit 13    */
                unsigned char B12           : 1;            /*    Bit 12    */
                unsigned char B11           : 1;            /*    Bit 11    */
                unsigned char B10           : 1;            /*    Bit 10    */
                unsigned char B9            : 1;            /*    Bit 9     */
                unsigned char B8            : 1;            /*    Bit 8     */
                unsigned char B7            : 1;            /*    Bit 7     */
                unsigned char B6            : 1;            /*    Bit 6     */
                unsigned char B5            : 1;            /*    Bit 5     */
                unsigned char B4            : 1;            /*    Bit 4     */
                unsigned char B3            : 1;            /*    Bit 3     */
                unsigned char B2            : 1;            /*    Bit 2     */
                unsigned char B1            : 1;            /*    Bit 1     */
                unsigned char B0            : 1;            /*    Bit 0     */
            }           BIT;                                /*              */
        }               PR;                                 /*              */
};                                                          /*              */
struct st_pc {                                              /* struct PC    */
        char            wk1[2];                             /*              *///FFFE3900
        union {                                             /* PCDR         *///FFFE3902
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char B15           : 1;            /*    Bit 15    */
                unsigned char B14           : 1;            /*    Bit 14    */
                unsigned char B13           : 1;            /*    Bit 13    */
                unsigned char B12           : 1;            /*    Bit 12    */
                unsigned char B11           : 1;            /*    Bit 11    */
                unsigned char B10           : 1;            /*    Bit 10    */
                unsigned char B9            : 1;            /*    Bit 9     */
                unsigned char B8            : 1;            /*    Bit 8     */
                unsigned char B7            : 1;            /*    Bit 7     */
                unsigned char B6            : 1;            /*    Bit 6     */
                unsigned char B5            : 1;            /*    Bit 5     */
                unsigned char B4            : 1;            /*    Bit 4     */
                unsigned char B3            : 1;            /*    Bit 3     */
                unsigned char B2            : 1;            /*    Bit 2     */
                unsigned char B1            : 1;            /*    Bit 1     */
                unsigned char B0            : 1;            /*    Bit 0     */
            }           BIT;                                /*              */
        }               DR;                                 /*              */
        char            wk2[26];                            /*              *///FFFE391E-FFFE3902-2
        union {                                             /* PCPR         *///FFFE391E
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*  High        */
                unsigned char L;                            /*  Low         */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char B15           : 1;            /*  Bit 15      */
                unsigned char B14           : 1;            /*  Bit 14      */
                unsigned char B13           : 1;            /*  Bit 13      */
                unsigned char B12           : 1;            /*  Bit 12      */
                unsigned char B11           : 1;            /*  Bit 11      */
                unsigned char B10           : 1;            /*  Bit 10      */
                unsigned char B9            : 1;            /*  Bit 9       */
                unsigned char B8            : 1;            /*  Bit 8       */
                unsigned char B7            : 1;            /*  Bit 7       */
                unsigned char B6            : 1;            /*  Bit 6       */
                unsigned char B5            : 1;            /*  Bit 5       */
                unsigned char B4            : 1;            /*  Bit 4       */
                unsigned char B3            : 1;            /*  Bit 3       */
                unsigned char B2            : 1;            /*  Bit 2       */
                unsigned char B1            : 1;            /*  Bit 1       */
                unsigned char B0            : 1;            /*  Bit 0       */
            }           BIT;                                /*              */
        }               PR;                                 /*              */
};                                                          /*              */
struct st_pd {                                              /* struct PD    */
        union {                                             /* PDDR         *///FFFE3980
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Word Access */
                unsigned short H;                           /*    High      */
                unsigned short L;                           /*    Low       */
            }           WORD;                               /*              */
            struct {                                        /*  Byte Access */
                unsigned char HH;                           /*    High,High */
                unsigned char HL;                           /*    High,Low  */
                unsigned char LH;                           /*    Low,High  */
                unsigned char LL;                           /*    Low,Low   */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char B31           : 1;            /*    Bit 31    */
                unsigned char B30           : 1;            /*    Bit 30    */
                unsigned char B29           : 1;            /*    Bit 29    */
                unsigned char B28           : 1;            /*    Bit 28    */
                unsigned char B27           : 1;            /*    Bit 27    */
                unsigned char B26           : 1;            /*    Bit 26    */
                unsigned char B25           : 1;            /*    Bit 25    */
                unsigned char B24           : 1;            /*    Bit 24    */
                unsigned char B23           : 1;            /*    Bit 23    */
                unsigned char B22           : 1;            /*    Bit 22    */
                unsigned char B21           : 1;            /*    Bit 21    */
                unsigned char B20           : 1;            /*    Bit 20    */
                unsigned char B19           : 1;            /*    Bit 19    */
                unsigned char B18           : 1;            /*    Bit 18    */
                unsigned char B17           : 1;            /*    Bit 17    */
                unsigned char B16           : 1;            /*    Bit 16    */
                unsigned char B15           : 1;            /*    Bit 15    */
                unsigned char B14           : 1;            /*    Bit 14    */
                unsigned char B13           : 1;            /*    Bit 13    */
                unsigned char B12           : 1;            /*    Bit 12    */
                unsigned char B11           : 1;            /*    Bit 11    */
                unsigned char B10           : 1;            /*    Bit 10    */
                unsigned char B9            : 1;            /*    Bit 9     */
                unsigned char B8            : 1;            /*    Bit 8     */
                unsigned char B7            : 1;            /*    Bit 7     */
                unsigned char B6            : 1;            /*    Bit 6     */
                unsigned char B5            : 1;            /*    Bit 5     */
                unsigned char B4            : 1;            /*    Bit 4     */
                unsigned char B3            : 1;            /*    Bit 3     */
                unsigned char B2            : 1;            /*    Bit 2     */
                unsigned char B1            : 1;            /*    Bit 1     */
                unsigned char B0            : 1;            /*    Bit 0     */
            }           BIT;                                /*              */
        }               DR;                                 /*              */
        char            wk1[24];                            /*              *///FFFE399C-FFFE3980-4
        union {                                             /* PDPR         *///FFFE399C
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Word Access */
                unsigned short H;                           /*    High      */
                unsigned short L;                           /*    Low       */
            }           WORD;                               /*              */
            struct {                                        /*  Byte Access */
                unsigned char HH;                           /*    High,High */
                unsigned char HL;                           /*    High,Low  */
                unsigned char LH;                           /*    Low,High  */
                unsigned char LL;                           /*    Low,Low   */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char B31           : 1;            /*    Bit 31    */
                unsigned char B30           : 1;            /*    Bit 30    */
                unsigned char B29           : 1;            /*    Bit 29    */
                unsigned char B28           : 1;            /*    Bit 28    */
                unsigned char B27           : 1;            /*    Bit 27    */
                unsigned char B26           : 1;            /*    Bit 26    */
                unsigned char B25           : 1;            /*    Bit 25    */
                unsigned char B24           : 1;            /*    Bit 24    */
                unsigned char B23           : 1;            /*    Bit 23    */
                unsigned char B22           : 1;            /*    Bit 22    */
                unsigned char B21           : 1;            /*    Bit 21    */
                unsigned char B20           : 1;            /*    Bit 20    */
                unsigned char B19           : 1;            /*    Bit 19    */
                unsigned char B18           : 1;            /*    Bit 18    */
                unsigned char B17           : 1;            /*    Bit 17    */
                unsigned char B16           : 1;            /*    Bit 16    */
                unsigned char B15           : 1;            /*    Bit 15    */
                unsigned char B14           : 1;            /*    Bit 14    */
                unsigned char B13           : 1;            /*    Bit 13    */
                unsigned char B12           : 1;            /*    Bit 12    */
                unsigned char B11           : 1;            /*    Bit 11    */
                unsigned char B10           : 1;            /*    Bit 10    */
                unsigned char B9            : 1;            /*    Bit 9     */
                unsigned char B8            : 1;            /*    Bit 8     */
                unsigned char B7            : 1;            /*    Bit 7     */
                unsigned char B6            : 1;            /*    Bit 6     */
                unsigned char B5            : 1;            /*    Bit 5     */
                unsigned char B4            : 1;            /*    Bit 4     */
                unsigned char B3            : 1;            /*    Bit 3     */
                unsigned char B2            : 1;            /*    Bit 2     */
                unsigned char B1            : 1;            /*    Bit 1     */
                unsigned char B0            : 1;            /*    Bit 0     */
            }           BIT;                                /*              */
        }               PR;                                 /*              */
};                                                          /*              */
struct st_pe {                                              /* struct PE    */
        char            wk1[2];                             /*              *///FFFE3A00
        union {                                             /* PEDR         *///FFFE3A02
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char B15           : 1;            /*    Bit 15    */
                unsigned char B14           : 1;            /*    Bit 14    */
                unsigned char B13           : 1;            /*    Bit 13    */
                unsigned char B12           : 1;            /*    Bit 12    */
                unsigned char B11           : 1;            /*    Bit 11    */
                unsigned char B10           : 1;            /*    Bit 10    */
                unsigned char B9            : 1;            /*    Bit 9     */
                unsigned char B8            : 1;            /*    Bit 8     */
                unsigned char B7            : 1;            /*    Bit 7     */
                unsigned char B6            : 1;            /*    Bit 6     */
                unsigned char B5            : 1;            /*    Bit 5     */
                unsigned char B4            : 1;            /*    Bit 4     */
                unsigned char B3            : 1;            /*    Bit 3     */
                unsigned char B2            : 1;            /*    Bit 2     */
                unsigned char B1            : 1;            /*    Bit 1     */
                unsigned char B0            : 1;            /*    Bit 0     */
            }           BIT;                                /*              */
        }               DR;                                 /*              */
        char            wk2[26];                            /*              *///FFFE3A1E-FFFE3A02-2
        union {                                             /* PEPR         *///FFFE3A1E
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                unsigned char H;                            /*    High      */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char B15           : 1;            /*    Bit 15    */
                unsigned char B14           : 1;            /*    Bit 14    */
                unsigned char B13           : 1;            /*    Bit 13    */
                unsigned char B12           : 1;            /*    Bit 12    */
                unsigned char B11           : 1;            /*    Bit 11    */
                unsigned char B10           : 1;            /*    Bit 10    */
                unsigned char B9            : 1;            /*    Bit 9     */
                unsigned char B8            : 1;            /*    Bit 8     */
                unsigned char B7            : 1;            /*    Bit 7     */
                unsigned char B6            : 1;            /*    Bit 6     */
                unsigned char B5            : 1;            /*    Bit 5     */
                unsigned char B4            : 1;            /*    Bit 4     */
                unsigned char B3            : 1;            /*    Bit 3     */
                unsigned char B2            : 1;            /*    Bit 2     */
                unsigned char B1            : 1;            /*    Bit 1     */
                unsigned char B0            : 1;            /*    Bit 0     */
            }           BIT;                                /*              */
        }               PR;                                 /*              */
};                                                          /*              */
struct st_pf {                                              /* struct PF    */
        char            wk1[2];                             /*              *///FFFE3A80
        union {                                             /* PFDR         *///FFFE3A82
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Byte Access */
                char    wk2[1];                             /*              */
                unsigned char L;                            /*    Low       */
            }           BYTE;                               /*              */
            struct {                                        /*  Bit Access  */
                unsigned char               : 8;            /*              */
                unsigned char B7            : 1;            /*    Bit 7     */
                unsigned char B6            : 1;            /*    Bit 6     */
                unsigned char B5            : 1;            /*    Bit 5     */
                unsigned char B4            : 1;            /*    Bit 4     */
                unsigned char B3            : 1;            /*    Bit 3     */
                unsigned char B2            : 1;            /*    Bit 2     */
                unsigned char B1            : 1;            /*    Bit 1     */
                unsigned char B0            : 1;            /*    Bit 0     */
            }           BIT;                                /*              */
        }               DR;                                 /*              */
};                                                          /*              */
struct st_usb {                                             /* struct USB   */
        union {                                             /* USBIFR0      *///FFFE7000
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char BRST          : 1;            /*    BRST      */
                unsigned char CFDN          : 1;            /*    CFDN      */
                unsigned char               : 2;            /*              */
                unsigned char SETC          : 1;            /*    SETC      */
                unsigned char SETI          : 1;            /*    SETI      */
                unsigned char VBUSMN        : 1;            /*    VBUSMN    */
                unsigned char VBUSF         : 1;            /*    VBUSF     */
            }           BIT;                                /*              */
        }               USBIFR0;                            /*              */
        union {                                             /* USBIFR1      *///FFFE7001
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 3;            /*              */
                unsigned char SOF           : 1;            /*    SOF       */
                unsigned char SETUPTS       : 1;            /*    SETUPTS   */
                unsigned char EP0oTS        : 1;            /*    EP0oTS    */
                unsigned char EP0iTR        : 1;            /*    EP0iTR    */
                unsigned char EP0iTS        : 1;            /*    EP0iTS    */
            }           BIT;                                /*              */
        }               USBIFR1;                            /*              */
        union {                                             /* USBIFR2      *///FFFE7002
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char EP3TR         : 1;            /*    EP3TR     */
                unsigned char EP3TS         : 1;            /*    EP3TS     */
                unsigned char EP2TR         : 1;            /*    EP2TR     */
                unsigned char EP2EMPTY      : 1;            /*    EP2EMPTY  */
                unsigned char EP2ALLEMP     : 1;            /*    EP2ALLEMP */
                unsigned char EP1FULL       : 1;            /*    EP1FULL   */
            }           BIT;                                /*              */
        }               USBIFR2;                            /*              */
        union {                                             /* USBIFR3      *///FFFE7003
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char EP6TR         : 1;            /*    EP6TR     */
                unsigned char EP6TS         : 1;            /*    EP6TS     */
                unsigned char EP5TR         : 1;            /*    EP5TR     */
                unsigned char EP5EMPTY      : 1;            /*    EP5EMPTY  */
                unsigned char EP5ALLEMP     : 1;            /*    EP5ALLEMP */
                unsigned char EP4FULL       : 1;            /*    EP4FULL   */
            }           BIT;                                /*              */
        }               USBIFR3;                            /*              */
        union {                                             /* USBIFR4      *///FFFE7004
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char EP9TR         : 1;            /*    EP9TR     */
                unsigned char EP9TS         : 1;            /*    EP9TS     */
                unsigned char EP8TR         : 1;            /*    EP8TR     */
                unsigned char EP8EMPTY      : 1;            /*    EP8EMPTY  */
                unsigned char               : 1;            /*              */
                unsigned char EP7FULL       : 1;            /*    EP7FULL   */
            }           BIT;                                /*              */
        }               USBIFR4;                            /*              */
        char            wk1[3];                             /*              *///FFFE7008-FFFE7004-1
        union {                                             /* USBIER0      *///FFFE7008
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char BRSTE         : 1;            /*    BRSTE     */
                unsigned char CFDFN         : 1;            /*    CFDFN     */
                unsigned char               : 2;            /*              */
                unsigned char SETCE         : 1;            /*    SETCE     */
                unsigned char SETIE         : 1;            /*    SETIE     */
                unsigned char               : 1;            /*              */
                unsigned char VBUSFE        : 1;            /*    VBUSFE    */
            }           BIT;                                /*              */
        }               USBIER0;                            /*              */
        union {                                             /* USBIER1      *///FFFE7009
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 3;            /*              */
                unsigned char SOFE          : 1;            /*    SOFE      */
                unsigned char SETUPTSE      : 1;            /*    SETUPTSE  */
                unsigned char EP0oTSE       : 1;            /*    EP0oTSE   */
                unsigned char EP0iTRE       : 1;            /*    EP0iTRE   */
                unsigned char EP0iTSE       : 1;            /*    EP0iTSE   */
            }           BIT;                                /*              */
        }               USBIER1;                            /*              */
        union {                                             /* USBIER2      *///FFFE700A
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char EP3TRE        : 1;            /*    EP3TRE    */
                unsigned char EP3TSE        : 1;            /*    EP3TSE    */
                unsigned char EP2TRE        : 1;            /*    EP2TRE    */
                unsigned char EP2EMPTYE     : 1;            /*    EP2EMPTYE */
                unsigned char EP2ALLEMPE    : 1;            /*    EP2ALLEMPE*/
                unsigned char EP1FULLE      : 1;            /*    EP1FULLE  */
            }           BIT;                                /*              */
        }               USBIER2;                            /*              */
        union {                                             /* USBIER3      *///FFFE700B
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char EP6TRE        : 1;            /*    EP6TRE    */
                unsigned char EP6TSE        : 1;            /*    EP6TSE    */
                unsigned char EP5TRE        : 1;            /*    EP5TRE    */
                unsigned char EP5EMPTYE     : 1;            /*    EP5EMPTYE */
                unsigned char EP5ALLEMPE    : 1;            /*    EP5ALLEMPE*/
                unsigned char EP4FULLE      : 1;            /*    EP4FULLE  */
            }           BIT;                                /*              */
        }               USBIER3;                            /*              */
        union {                                             /* USBIER4      *///FFFE700C
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char EP9TRE        : 1;            /*    EP9TRE    */
                unsigned char EP9TSE        : 1;            /*    EP9TSE    */
                unsigned char EP8TRE        : 1;            /*    EP8TRE    */
                unsigned char EP8EMPTYE     : 1;            /*    EP8EMPTYE */
                unsigned char               : 1;            /*              */
                unsigned char EP7FULLE      : 1;            /*    EP7FULLE  */
            }           BIT;                                /*              */
        }               USBIER4;                            /*              */
        char            wk2[3];                             /*              *///FFFE7010-FFFE700C-1
        union {                                             /* USBISR0      *///FFFE7010
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char BRSTS         : 1;            /*    BRSTS     */
                unsigned char CFDNS         : 1;            /*    CFDNS     */
                unsigned char               : 2;            /*              */
                unsigned char SETCS         : 1;            /*    SETCS     */
                unsigned char SETIS         : 1;            /*    SETIS     */
                unsigned char               : 1;            /*              */
                unsigned char VBUSFS        : 1;            /*    VBUSFS    */
            }           BIT;                                /*              */
        }               USBISR0;                            /*              */
        union {                                             /* USBISR1      *///FFFE7011
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 3;            /*              */
                unsigned char SOFS          : 1;            /*    SOFS      */
                unsigned char SETUPTSS      : 1;            /*    SETUPTSS  */
                unsigned char EP0oTSS       : 1;            /*    EP0oTSS   */
                unsigned char EP0iTRS       : 1;            /*    EP0iTRS   */
                unsigned char EP0iTSS       : 1;            /*    EP0iTSS   */
            }           BIT;                                /*              */
        }               USBISR1;                            /*              */
        union {                                             /* USBISR2      *///FFFE7012
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char EP3TRS        : 1;            /*    EP3TRS    */
                unsigned char EP3TSS        : 1;            /*    EP3TSS    */
                unsigned char EP2TRS        : 1;            /*    EP2TRS    */
                unsigned char EP2EMPTYS     : 1;            /*    EP2EMPTYS */
                unsigned char EP2ALLEMPS    : 1;            /*    EP2ALLEMPS*/
                unsigned char EP1FULLS      : 1;            /*    EP1FULLS  */
            }           BIT;                                /*              */
        }               USBISR2;                            /*              */
        union {                                             /* USBISR3      *///FFFE7013
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char EP6TRS        : 1;            /*    EP6TRS    */
                unsigned char EP6TSS        : 1;            /*    EP6TSS    */
                unsigned char EP5TRS        : 1;            /*    EP5TRS    */
                unsigned char EP5EMPTYS     : 1;            /*    EP5EMPTYS */
                unsigned char EP5ALLEMPS    : 1;            /*    EP5ALLEMPS*/
                unsigned char EP4FULLE      : 1;            /*    EP4FULLS  */
            }           BIT;                                /*              */
        }               USBISR3;                            /*              */
        union {                                             /* USBISR4      *///FFFE7014
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 2;            /*              */
                unsigned char EP9TRS        : 1;            /*    EP9TRS    */
                unsigned char EP9TSS        : 1;            /*    EP9TSS    */
                unsigned char EP8TRS        : 1;            /*    EP8TRS    */
                unsigned char EP8EMPTYS     : 1;            /*    EP8EMPTYS */
                unsigned char               : 1;            /*              */
                unsigned char EP7FULLS      : 1;            /*    EP7FULLS  */
            }           BIT;                                /*              */
        }               USBISR4;                            /*              */
        char            wk3[11];                            /*              *///FFFE7020-FFFE7014-1
        unsigned char   USBEPDR0i;                          /* USBEPDR0i    *///FFFE7020
        char            wk4[3];                             /*              *///FFFE7024-FFFE7020-1
        unsigned char   USBEPDR0o;                          /* USBEPDR0o    *///FFFE7024
        char            wk5[3];                             /*              *///FFFE7028-FFFE7024-1
        unsigned char   USBEPDR0s;                          /* USBEPDR0s    *///FFFE7028
        char            wk6[7];                             /*              *///FFFE7030-FFFE7028-1
        unsigned char   USBEPDR1;                           /* USBEPDR1     *///FFFE7030
        char            wk7[3];                             /*              *///FFFE7034-FFFE7030-1
        unsigned char   USBEPDR2;                           /* USBEPDR2     *///FFFE7034
        char            wk8[3];                             /*              *///FFFE7038-FFFE7034-1
        unsigned char   USBEPDR3;                           /* USBEPDR3     *///FFFE7038
        char            wk9[7];                             /*              *///FFFE7040-FFFE7038-1
        unsigned char   USBEPDR4;                           /* USBEPDR4     *///FFFE7040
        char            wk10[3];                            /*              *///FFFE7044-FFFE7040-1
        unsigned char   USBEPDR5;                           /* USBEPDR5     *///FFFE7044
        char            wk11[3];                            /*              *///FFFE7048-FFFE7044-1
        unsigned char   USBEPDR6;                           /* USBEPDR6     *///FFFE7048
        char            wk12[7];                            /*              *///FFFE7050-FFFE7048-1
        unsigned char   USBEPDR7;                           /* USBEPDR7     *///FFFE7050
        char            wk13[3];                            /*              *///FFFE7054-FFFE7050-1
        unsigned char   USBEPDR8;                           /* USBEPDR8     *///FFFE7054
        char            wk14[3];                            /*              *///FFFE7058-FFFE7054-1
        unsigned char   USBEPDR9;                           /* USBEPDR9     *///FFFE7058
        char            wk15[39];                           /*              *///FFFE7080-FFFE7058-1
        unsigned char   USBEPSZ0o;                          /* USBEPSZ0o    *///FFFE7080
        unsigned char   USBEPSZ1;                           /* USBEPSZ1     *///FFFE7081
        unsigned char   USBEPSZ4;                           /* USBEPSZ4     *///FFFE7082
        unsigned char   USBEPSZ7;                           /* USBEPSZ7     *///FFFE7083
        char            wk16[4];                            /*              *///FFFE7088-FFFE7083-1
        union {                                             /* USBDASTS0    *///FFFE7088
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 7;            /*              */
                unsigned char EP0iDE        : 1;            /*    EP0iDE    */
            }           BIT;                                /*              */
        }               USBDASTS0;                          /*              */
        union {                                             /* USBDASTS1    *///FFFE7089
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char EP3DE         : 1;            /*    EP3DE     */
                unsigned char EP2DE         : 1;            /*    EP2DE     */
                unsigned char               : 1;            /*              */
            }           BIT;                                /*              */
        }               USBDASTS1;                          /*              */
        union {                                             /* USBDASTS2    *///FFFE708A
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char EP6DE         : 1;            /*    EP6DE     */
                unsigned char EP5DE         : 1;            /*    EP5DE     */
                unsigned char               : 1;            /*              */
            }           BIT;                                /*              */
        }               USBDASTS2;                          /*              */
        union {                                             /* USBDASTS3    *///FFFE708B
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char EP9DE         : 1;            /*    EP9DE     */
                unsigned char EP8DE         : 1;            /*    EP8DE     */
                unsigned char               : 1;            /*              */
            }           BIT;                                /*              */
        }               USBDASTS3;                          /*              */
        char            wk17[4];                            /*              *///FFFE7090-FFFE708B-1
        union {                                             /* USBTRG0      *///FFFE7090
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char EP0sRDFN      : 1;            /*    EP0SRDFN  */
                unsigned char EP0oRDFN      : 1;            /*    EP0ORDFN  */
                unsigned char EP0iPKTE      : 1;            /*    EP0IPKTE  */
            }           BIT;                                /*              */
        }               USBTRG0;                            /*              */
        union {                                             /* USBTRG1      *///FFFE7091
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char EP3PKTE       : 1;            /*    EP3PKTE   */
                unsigned char EP2PKTE       : 1;            /*    EP2PKTE   */
                unsigned char EP1RDFN       : 1;            /*    EP1RDFN   */
            }           BIT;                                /*              */
        }               USBTRG1;                            /*              */
        union {                                             /* USBTRG2      *///FFFE7092
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char EP6PKTE       : 1;            /*    EP6PKTE   */
                unsigned char EP5PKTE       : 1;            /*    EP5PKTE   */
                unsigned char EP4RDFN       : 1;            /*    EP4RDFN   */
            }           BIT;                                /*              */
        }               USBTRG2;                            /*              */
        union {                                             /* USBTRG3      *///FFFE7093
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char EP9PKTE       : 1;            /*    EP9PKTE   */
                unsigned char EP8PKTE       : 1;            /*    EP8PKTE   */
                unsigned char EP7RDFN       : 1;            /*    EP7RDFN   */
            }           BIT;                                /*              */
        }               USBTRG3;                            /*              */
        char            wk18[4];                            /*              *///FFFE7098-FFFE7093-1
        union {                                             /* USBFCLR0     *///FFFE7098
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 6;            /*              */
                unsigned char EP0oCLR       : 1;            /*    EP0oCLR   */
                unsigned char EP0iCLR       : 1;            /*    EP0iCLR   */
            }           BIT;                                /*              */
        }               USBFCLR0;                           /*              */
        union {                                             /* USBFCLR1     *///FFFE7099
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char EP3CLR        : 1;            /*    EP3CLR    */
                unsigned char EP2CLR        : 1;            /*    EP2CLR    */
                unsigned char EP1CLR        : 1;            /*    EP1CLR    */
            }           BIT;                                /*              */
        }               USBFCLR1;                           /*              */
        union {                                             /* USBFCLR2     *///FFFE709A
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char EP6CLR        : 1;            /*    EP6CLR    */
                unsigned char EP5CLR        : 1;            /*    EP5CLR    */
                unsigned char EP4CLR        : 1;            /*    EP4CLR    */
            }           BIT;                                /*              */
        }               USBFCLR2;                           /*              */
        union {                                             /* USBFCLR3     *///FFFE709B
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char EP9CLR        : 1;            /*    EP9CLR    */
                unsigned char EP8CLR        : 1;            /*    EP8CLR    */
                unsigned char EP7CLR        : 1;            /*    EP7CLR    */
            }           BIT;                                /*              */
        }               USBFCLR3;                           /*              */
        char            wk19[4];                            /*              *///FFFE70A0-FFFE709B-1
        union {                                             /* USBEPSTL0    *///FFFE70A0
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 3;            /*              */
                unsigned char EP0STLC       : 1;            /*    EP0STLC   */
                unsigned char               : 3;            /*              */
                unsigned char EP0STLS       : 1;            /*    EP0STLS   */
            }           BIT;                                /*              */
        }               USBEPSTL0;                          /*              */
        union {                                             /* USBEPSTL1    *///FFFE70A1
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char EP3STLC       : 1;            /*    EP3STLC   */
                unsigned char EP2STLC       : 1;            /*    EP2STLC   */
                unsigned char EP1STLC       : 1;            /*    EP1STLC   */
                unsigned char               : 1;            /*              */
                unsigned char EP3STLS       : 1;            /*    EP3STLS   */
                unsigned char EP2STLS       : 1;            /*    EP2STLS   */
                unsigned char EP1STLS       : 1;            /*    EP1STLS   */
            }           BIT;                                /*              */
        }               USBEPSTL1;                          /*              */
        union {                                             /* USBEPSTL2    *///FFFE70A2
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char EP6STLC       : 1;            /*    EP6STLC   */
                unsigned char EP5STLC       : 1;            /*    EP5STLC   */
                unsigned char EP4STLC       : 1;            /*    EP4STLC   */
                unsigned char               : 1;            /*              */
                unsigned char EP6STLS       : 1;            /*    EP6STLS   */
                unsigned char EP5STLS       : 1;            /*    EP5STLS   */
                unsigned char EP4STLS       : 1;            /*    EP4STLS   */
            }           BIT;                                /*              */
        }               USBEPSTL2;                          /*              */
        union {                                             /* USBEPSTL3    *///FFFE70A3
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char EP9STLC       : 1;            /*    EP9STLC   */
                unsigned char EP8STLC       : 1;            /*    EP8STLC   */
                unsigned char EP7STLC       : 1;            /*    EP7STLC   */
                unsigned char               : 1;            /*              */
                unsigned char EP9STLS       : 1;            /*    EP9STLS   */
                unsigned char EP8STLS       : 1;            /*    EP8STLS   */
                unsigned char EP7STLS       : 1;            /*    EP7STLS   */
            }           BIT;                                /*              */
        }               USBEPSTL3;                          /*              */
        char            wk20[5];                            /*              *///FFFE70A9-FFFE70A3-1
        union {                                             /* USBSTLSR1    *///FFFE70A9
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char EP3ASCE       : 1;            /*    EP3ASCE   */
                unsigned char EP2ASCE       : 1;            /*    EP2ASCE   */
                unsigned char EP1ASCE       : 1;            /*    EP1ASCE   */
                unsigned char               : 1;            /*              */
                unsigned char EP3STLST      : 1;            /*    EP3STLST  */
                unsigned char EP2STLST      : 1;            /*    EP2STLST  */
                unsigned char EP1STLST      : 1;            /*    EP1STLST  */
            }           BIT;                                /*              */
        }               USBSTLSR1;                          /*              */
        union {                                             /* USBSTLSR2    *///FFFE70AA
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char EP6ASCE       : 1;            /*    EP6ASCE   */
                unsigned char EP5ASCE       : 1;            /*    EP5ASCE   */
                unsigned char EP4ASCE       : 1;            /*    EP4ASCE   */
                unsigned char               : 1;            /*              */
                unsigned char EP6STLST      : 1;            /*    EP6STLST  */
                unsigned char EP5STLST      : 1;            /*    EP5STLST  */
                unsigned char EP4STLST      : 1;            /*    EP4STLST  */
            }           BIT;                                /*              */
        }               USBSTLSR2;                          /*              */
        union {                                             /* USBSTLSR3    *///FFFE70AB
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 1;            /*              */
                unsigned char EP9ASCE       : 1;            /*    EP9ASCE   */
                unsigned char EP8ASCE       : 1;            /*    EP8ASCE   */
                unsigned char EP7ASCE       : 1;            /*    EP7ASCE   */
                unsigned char               : 1;            /*              */
                unsigned char EP9STLST      : 1;            /*    EP9STLST  */
                unsigned char EP8STLST      : 1;            /*    EP8STLST  */
                unsigned char EP7STLST      : 1;            /*    EP7STLST  */
            }           BIT;                                /*              */
        }               USBSTLSR3;                          /*              */
        char            wk21[4];                            /*              *///FFFE70B0-FFFE70AB-1
        union {                                             /* USBDMAR      *///FFFE70B0
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 3;            /*              */
                unsigned char EP5DMAE       : 1;            /*    EP5DMAE   */
                unsigned char EP4DMAE       : 1;            /*    EP4DMAE   */
                unsigned char               : 1;            /*              */
                unsigned char EP2DMAE       : 1;            /*    EP2DMAE   */
                unsigned char EP1DMAE       : 1;            /*    EP1DMAE   */
            }           BIT;                                /*              */
        }               USBDMAR;                            /*              */
        char            wk22[3];                            /*              *///FFFE70B4-FFFE70B0-1
        union {                                             /* USBCVR       *///FFFE70B4
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char CNFV          : 2;            /*    CNFV      */
                unsigned char INTV          : 2;            /*    INTV      */
                unsigned char               : 1;            /*              */
                unsigned char ALTV          : 3;            /*    ALTV      */
            }           BIT;                                /*              */
        }               USBCVR;                             /*              */
        char            wk23[3];                            /*              *///FFFE70B8-FFFE70B4-1
        union {                                             /* USBCTLR      *///FFFE70B8
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 6;            /*              */
                unsigned char EP0ASCE       : 1;            /*    EP0ASCE   */
                unsigned char PRTRST        : 1;            /*    PRTRST    */
            }           BIT;                                /*              */
        }               USBCTLR;                            /*              */
        char            wk24[7];                            /*              *///FFFE70C0-FFFE70B8-1
        unsigned char   USBEPIR;                            /* USBEPIR      *///FFFE70C0
        char            wk25[15];                           /*              *///FFFE70D0-FFFE70C0-1
        union {                                             /* USBTRNTREG0  *///FFFE70D0
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char PTSTE         : 1;            /*    PTSTE     */
                unsigned char               : 3;            /*              */
                unsigned char SUSPEND       : 1;            /*    SUSPEND   */
                unsigned char txenl         : 1;            /*    txenl     */
                unsigned char txse0         : 1;            /*    txse0     */
                unsigned char txdata        : 1;            /*    txdata    */
            }           BIT;                                /*              */
        }               USBTRNTREG0;                        /*              */
        union {                                             /* USBTRNTREG1  *///FFFE70D1
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 5;            /*              */
                unsigned char xver_data     : 1;            /*    xver_data */
                unsigned char dpls          : 1;            /*    dpls      */
                unsigned char dmns          : 1;            /*    dmns      */
            }           BIT;                                /*              */
        }               USBTRNTREG1;                        /*              */
};                                                          /*              */
struct st_etherc {                                          /* struct EtherC*/
        union {                                             /* ECMR         *///FFFC3100
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :11;            /*              */
                unsigned int TPC            : 1;            /*    TPC       */
                unsigned int ZPF            : 1;            /*    ZPF       */
                unsigned int PFR            : 1;            /*    PFR       */
                unsigned int RXF            : 1;            /*    RXF       */
                unsigned int TXF            : 1;            /*    TXF       */
                unsigned int                : 3;            /*              */
                unsigned int PRCEF          : 1;            /*    PRCEF     */
                unsigned int                : 2;            /*              */
                unsigned int MPDE           : 1;            /*    MPDE      */
                unsigned int                : 2;            /*              */
                unsigned int RE             : 1;            /*    RE        */
                unsigned int TE             : 1;            /*    TE        */
                unsigned int                : 1;            /*              */
                unsigned int ILB            : 1;            /*    ILB       */
                unsigned int ELB            : 1;            /*    ELB       */
                unsigned int DM             : 1;            /*    DM        */
                unsigned int PRM            : 1;            /*    PRM       */
            }           BIT;                                /*              */
        }               ECMR;                               /*              */
        char            wk1[4];                             /*              *///FFFC3108-FFFC3100-4
        union {                                             /* RFLR         *///FFFC3108
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :20;            /*              */
                unsigned int RFL            :12;            /*    RFL       */
            }           BIT;                                /*              */
        }               RFLR;                               /*              */
        char            wk2[4];                             /*              *///FFFC3110-FFFC3108-4
        union {                                             /* ECSR         *///FFFC3110
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :26;            /*              */
                unsigned int BFR            : 1;            /*    BFR       */
                unsigned int PSRTO          : 1;            /*    PSRTO     */
                unsigned int                : 1;            /*              */
                unsigned int LCHNG          : 1;            /*    LCHNG     */
                unsigned int MPD            : 1;            /*    MPD       */
                unsigned int ICD            : 1;            /*    ICD       */
            }           BIT;                                /*              */
        }               ECSR;                               /*              */
        char            wk3[4];                             /*              *///FFFC3118-FFFC3110-4
        union {                                             /* ECSIPR       *///FFFC3118
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :26;            /*              */
                unsigned int BFSIPR         : 1;            /*    BFSIPR    */
                unsigned int PSRTOIP        : 1;            /*    PSRTOIP   */
                unsigned int                : 1;            /*              */
                unsigned int LCHNGIP        : 1;            /*    LCHNGIP   */
                unsigned int MPDIP          : 1;            /*    MPDIP     */
                unsigned int ICDIP          : 1;            /*    ICDIP     */
            }           BIT;                                /*              */
        }               ECSIPR;                             /*              */
        char            wk4[4];                             /*              *///FFFC3120-FFFC3118-4
        union {                                             /* PIR          *///FFFC3120
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :28;            /*              */
                unsigned int MDI            : 1;            /*    MDI       */
                unsigned int MDO            : 1;            /*    MDO       */
                unsigned int MMD            : 1;            /*    MMD       */
                unsigned int MDC            : 1;            /*    MDC       */
            }           BIT;                                /*              */
        }               PIR;                                /*              */
        char            wk5[4];                             /*              *///FFFC3128-FFFC3120-4
        union {                                             /* PSR          *///FFFC3128
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :31;            /*              */
                unsigned int LMON           : 1;            /*    LMON      */
            }           BIT;                                /*              */
        }               PSR;                                /*              */
        char            wk6[20];                            /*              *///FFFC3140-FFFC3128-4
        union {                                             /* RDMLR        *///FFFC3140
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :12;            /*              */
                unsigned int RMD            :20;            /*    RMD       */
            }           BIT;                                /*              */
        }               RDMLR;                              /*              */
        char            wk7[12];                            /*              *///FFFC3150-FFFC3140-4
        union {                                             /* IPGR         *///FFFC3150
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :27;            /*              */
                unsigned int IPG            : 5;            /*    IPG       */
            }           BIT;                                /*              */
        }               IPGR;                               /*              */
        union {                                             /* APR          *///FFFC3154
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :16;            /*              */
                unsigned int AP             :16;            /*    AP        */
            }           BIT;                                /*              */
        }               APR;                                /*              */
        union {                                             /* MPR          *///FFFC3158
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :16;            /*              */
                unsigned int MP             :16;            /*    MP        */
            }           BIT;                                /*              */
        }               MPR;                                /*              */
        char            wk8[4];                             /*              *///FFFC3160-FFFC3158-4
        union {                                             /* RFCF         *///FFFC3160
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :24;            /*              */
                unsigned int RPAUSE         : 8;            /*    RPAUSE    */
            }           BIT;                                /*              */
        }               RFCF;                               /*              */
        union {                                             /* TPAUSER      *///FFFC3164
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :16;            /*              */
                unsigned int TPAUSE         :16;            /*    TPAUSE    */
            }           BIT;                                /*              */
        }               TPAUSER;                            /*              */
        union {                                             /* TPAUSECR     *///FFFC3168
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :24;            /*              */
                unsigned int TXP            : 8;            /*    TXP       */
            }           BIT;                                /*              */
        }               TPAUSECR;                           /*              */
        union {                                             /* BCFRR        *///FFFC316C
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :16;            /*              */
                unsigned int BCF            :16;            /*    BCF       */
            }           BIT;                                /*              */
        }               BCFRR;                              /*              */
        char            wk9[80];                            /*              *///FFFC31C0-FFFC316C-4
        unsigned int    MAHR;                               /* MAHR         *///FFFC31C0
        char            wk10[4];                            /*              *///FFFC31C8-FFFC31C0-4
        union {                                             /* MALR         *///FFFC31C8
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :16;            /*              */
                unsigned int MA             :16;            /*    MA        */
            }           BIT;                                /*              */
        }               MALR;                               /*              */
        char            wk11[4];                            /*              *///FFFC31D0-FFFC31C8-4
        unsigned int    TROCR;                              /* TROCR        *///FFFC31D0
        unsigned int    CDCR;                               /* CDCR         *///FFFC31D4
        unsigned int    LCCR;                               /* LCCR         *///FFFC31D8
        unsigned int    CNDCR;                              /* CNDCR        *///FFFC31DC
        char            wk12[4];                            /*              *///FFFC31E4-FFFC31DC-4
        unsigned int    CEFCR;                              /* CEFCR        *///FFFC31E4
        unsigned int    FRECR;                              /* FRECR        *///FFFC31E8
        unsigned int    TSFRCR;                             /* TSFRCR       *///FFFC31EC
        unsigned int    TLFRCR;                             /* TLFRCR       *///FFFC31F0
        unsigned int    RFCR;                               /* RFCR         *///FFFC31F4
        unsigned int    MAFCR;                              /* MAFCR        *///FFFC31F8
};                                                          /*              */
struct st_edmac {                                           /* struct EDMAC */
        union {                                             /* EDMR         *///FFFC3000
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :25;            /*              */
                unsigned int DE             : 1;            /*    DE        */
                unsigned int DL             : 2;            /*    DL        */
                unsigned int                : 3;            /*              */
                unsigned int SWR            : 1;            /*    SWR       */
            } BIT;                                          /*              */
        } EDMR;                                             /*              */
        char            wk1[4];                             /*              *///FFFC3008-FFFC3004-4
        union {                                             /* EDTRR        *///FFFC3008
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :31;            /*              */
                unsigned int TR             : 1;            /*    TR        */
            } BIT;                                          /*              */
        } EDTRR;                                            /*              */
        char            wk2[4];                             /*              *///FFFC3010-FFFC3008-4
        union {                                             /* EDRRR        *///FFFC3008
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :31;            /*              */
                unsigned int RR             : 1;            /*    RR        */
            } BIT;                                          /*              */
        } EDRRR;                                            /*              */
        char            wk3[4];                             /*              *///FFFC3018-FFFC3008-4
        void            *TDLAR;                             /* TDLAR        *///FFFC3018
        char            wk4[4];                             /*              *///FFFC3020-FFFC3018-4
        void            *RDLAR;                             /* RDLAR        *///FFFC3020
        char            wk5[4];                             /*              *///FFFC3028-FFFC3020-4
        union {                                             /* EESR         *///FFFC3028
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                : 1;            /*              */
                unsigned int TWB            : 1;            /*    TWB       */
                unsigned int                : 3;            /*              */
                unsigned int TABT           : 1;            /*    TABT      */
                unsigned int RABT           : 1;            /*    RABT      */
                unsigned int RFCOF          : 1;            /*    RFCOF     */
                unsigned int ADE            : 1;            /*    ADE       */
                unsigned int ECI            : 1;            /*    ECI       */
                unsigned int TC             : 1;            /*    TC        */
                unsigned int TDE            : 1;            /*    TDE       */
                unsigned int TFUF           : 1;            /*    TFUF      */
                unsigned int FR             : 1;            /*    FR        */
                unsigned int RDE            : 1;            /*    RDE       */
                unsigned int RFOF           : 1;            /*    RFOF      */
                unsigned int                : 4;            /*              */
                unsigned int CND            : 1;            /*    CND       */
                unsigned int DLC            : 1;            /*    DLC       */
                unsigned int CD             : 1;            /*    CD        */
                unsigned int TRO            : 1;            /*    TRO       */
                unsigned int RMAF           : 1;            /*    RMAF      */
                unsigned int                : 2;            /*              */
                unsigned int RRF            : 1;            /*    RRF       */
                unsigned int RTLF           : 1;            /*    RTLF      */
                unsigned int RTSF           : 1;            /*    RTSF      */
                unsigned int PRE            : 1;            /*    PRE       */
                unsigned int CERF           : 1;            /*    CERF      */
            }           BIT;                                /*              */
        }               EESR;                               /*              */
        char            wk6[4];                             /*              *///FFFC3030-FFFC3028-4
        union {                                             /* EESIPR       *///FFFC3030
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                : 1;            /*              */
                unsigned int TWBIP          : 1;            /*    TWBIP     */
                unsigned int                : 3;            /*              */
                unsigned int TABTIP         : 1;            /*    TABTIP    */
                unsigned int RABTIP         : 1;            /*    RABTIP    */
                unsigned int RFCOFIP        : 1;            /*    RFCOFIP   */
                unsigned int ADEIP          : 1;            /*    ADEIP     */
                unsigned int ECIIP          : 1;            /*    ECIIP     */
                unsigned int TCIP           : 1;            /*    TCIP      */
                unsigned int TDEIP          : 1;            /*    TDEIP     */
                unsigned int TFUFIP         : 1;            /*    TFUFIP    */
                unsigned int FRIP           : 1;            /*    FRIP      */
                unsigned int RDEIP          : 1;            /*    RDEIP     */
                unsigned int RFOFIP         : 1;            /*    RFOFIP    */
                unsigned int                : 4;            /*              */
                unsigned int CNDIP          : 1;            /*    CNDIP     */
                unsigned int DLCIP          : 1;            /*    DLCIP     */
                unsigned int CDIP           : 1;            /*    CDIP      */
                unsigned int TROIP          : 1;            /*    TROIP     */
                unsigned int RMAFIP         : 1;            /*    RMAFIP    */
                unsigned int                : 2;            /*              */
                unsigned int RRFIP          : 1;            /*    RRFIP     */
                unsigned int RTLFIP         : 1;            /*    RTLFIP    */
                unsigned int RTSFIP         : 1;            /*    RTSFIP    */
                unsigned int PREIP          : 1;            /*    PREIP     */
                unsigned int CERFIP         : 1;            /*    CERFIP    */
            }           BIT;                                /*              */
        }               EESIPR;                             /*              */
        char            wk7[4];                             /*              *///FFFC3038-FFFC3030-4
        union {                                             /* TRSCER       *///FFFC3038
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :20;            /*              */
                unsigned int CNDCE          : 1;            /*    CNDCE     */
                unsigned int DLCCE          : 1;            /*    DLCCE     */
                unsigned int CDCE           : 1;            /*    CDCE      */
                unsigned int TROCE          : 1;            /*    TROCE     */
                unsigned int RMAFCE         : 1;            /*    RMAFCE    */
                unsigned int                : 2;            /*              */
                unsigned int RRFCE          : 1;            /*    RRFCE     */
                unsigned int RTLFCE         : 1;            /*    RTLFCE    */
                unsigned int RTSFCE         : 1;            /*    RTSFCE    */
                unsigned int PRECE          : 1;            /*    PRECE     */
                unsigned int CERFCE         : 1;            /*    CERFCE    */
            }           BIT;                                /*              */
        }               TRSCER;                             /*              */
        char            wk8[4];                             /*              *///FFFC3040-FFFC3038-4
        union {                                             /* RMFCR        *///FFFC3040
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned short              :16;            /*              */
                unsigned short MFC          :16;            /*    MFC       */
            }           BIT;                                /*              */
        }               RMFCR;                              /*              */
        char            wk9[4];                             /*              *///FFFC3048-FFFC3040-4
        union {                                             /* TFTR         *///FFFC3048
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :21;            /*              */
                unsigned int TFT            :11;            /*    TFT       */
            }           BIT;                                /*              */
        }               TFTR;                               /*              */
        char            wk10[4];                            /*              *///FFFC3050-FFFC3048-4
        union {                                             /* FDR          *///FFFC3050
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :19;            /*              */
                unsigned int TFD            : 5;            /*    TFD       */
                unsigned int                : 3;            /*              */
                unsigned int RFD            : 5;            /*    RFD       */
            }           BIT;                                /*              */
        }               FDR;                                /*              */
        char            wk11[4];                            /*              *///FFFC3058-FFFC3050-4
        union {                                             /* RMCR         *///FFFC3058
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :30;            /*              */
                unsigned int RNC            : 1;            /*    RNC       */
                unsigned int RNR            : 1;            /*    RNR       */
            }           BIT;                                /*              */
        }               RMCR;                               /*              */
        char            wk12[8];                            /*              *///FFFC3064-FFFC3058-4
        union {                                             /* TFUCR        *///FFFC3064
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :16;            /*              */
                unsigned int UNDER          :16;            /*    UNDER     */
            }           BIT;                                /*              */
        }               TFUCR;                              /*              */
        union {                                             /* RFOCR        *///FFFC3068
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :16;            /*              */
                unsigned int OVER           :16;            /*    OVER      */
            }           BIT;                                /*              */
        }               RFOCR;                              /*              */
        union {                                             /* IOSR         *///FFFC306C
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :31;            /*              */
                unsigned int ELB            : 1;            /*    ELB       */
            }           BIT;                                /*              */
        }               IOSR;                               /*              */
        union {                                             /* FCFTR        *///FFFC3070
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :13;            /*              */
                unsigned int RFFO           : 3;            /*    RFFO      */
                unsigned int                :13;            /*              */
                unsigned int RFDO           : 3;            /*    RFDO      */
            }           BIT;                                /*              */
        }               FCFTR;                              /*              */
        char            wk13[8];                            /*              *///FFFC307C-FFFC3070-4
        union {                                             /* TRIMD        *///FFFC307C
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :27;            /*              */
                unsigned int TIM            : 1;            /*    TIM       */
                unsigned int                : 3;            /*              */
                unsigned int TIS            : 1;            /*    TIS       */
            }           BIT;                                /*              */
        }               TRIMD;                              /*              */
        char            wk14[72];                           /*              *///FFFC30C8-FFFC307C-4
        unsigned int    RBWAR;                              /* RBWAR        *///FFFC30C8
        unsigned int    RDFAR;                              /* RDFAR        *///FFFC30CC
        char            wk15[4];                            /*              *///FFFC30D4-FFFC30CC-4
        unsigned int    TBRAR;                              /* TBRAR        *///FFFC30D4
        unsigned int    TDFAR;                              /* TDFAR        *///FFFC30D8
        char            wk16[8];                            /*              *///FFFC30E4-FFFC30D8-4
        union {                                             /* EDOCR        *///FFFC30E4
            unsigned int LONG;                              /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :28;            /*              */
                unsigned int FEC            : 1;            /*    FEC       */
                unsigned int AEC            : 1;            /*    AEC       */
                unsigned int EDH            : 1;            /*    EDH       */
                unsigned int NMIE           : 1;            /*    NMIE      */
            }           BIT;                                /*              */
        }               EDOCR;                              /*              */
};                                                          /*              */
struct st_fld {                                             /* struct FLD   */
        union {                                             /* FPMON        *///FFFFA800
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char FWE           : 1;            /*    FWE       */
            }           BIT;                                /*              */
        }               FPMON;                              /*              */
        char            wk1[1];                             /*              *///FFFFA802-FFFFA800-1
        union {                                             /* FMODR        *///FFFFA802
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 3;            /*              */
                unsigned char FRDMD         : 1;            /*    FRDMD     */
            }           BIT;                                /*              */
        }               FMODR;                              /*              */
        char            wk2[13];                            /*              *///FFFFA810-FFFFA802-1
        union {                                             /* FASTAT       *///FFFFA810
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char ROMAE         : 1;            /*    ROMAE     */
                unsigned char               : 2;            /*              */
                unsigned char CMDLK         : 1;            /*    CMDLK     */
                unsigned char EEPAE         : 1;            /*    EEPAE     */
                unsigned char EEPIFE        : 1;            /*    EEPIFE    */
                unsigned char EEPRPE        : 1;            /*    EEPRPE    */
                unsigned char EEPWPE        : 1;            /*    EEPWPE    */
            }           BIT;                                /*              */
        }               FASTAT;                             /*              */
        union {                                             /* FAEINT       *///FFFFA811
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char ROMAIE        : 1;            /*    ROMAIE    */
                unsigned char               : 2;            /*              */
                unsigned char CMDLKIE       : 1;            /*    CMDLKIE   */
                unsigned char EEPAEIE       : 1;            /*    EEPAEIE   */
                unsigned char EEPIFEIE      : 1;            /*    EEPIFEIE  */
                unsigned char EEPRPEIE      : 1;            /*    EEPRPEIE  */
                unsigned char EEPWPEIE      : 1;            /*    EEPWPEIE  */
            }           BIT;                                /*              */
        }               FAEINT;                             /*              */
        char            wk3[14];                            /*              *///FFFFA820-FFFFA811-1
        union {                                             /* ROMMAT       *///FFFFA820
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned char KEY           : 8;            /*    KEY       */
                unsigned char               : 7;            /*              */
                unsigned char ROMSEL        : 1;            /*    ROMSEL    */
            }           BIT;                                /*              */
        }               ROMMAT;                             /*              */
        char            wk4[30];                            /*              *///FFFFA840-FFFFA820-2
        union {                                             /* EEPRE0       *///FFFFA840
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned char KEY           : 8;            /*    KEY       */
                unsigned char               : 4;            /*              */
                unsigned char DBRE0         : 4;            /*    DBRE0     */
            }           BIT;                                /*              */
        }               EEPRE0;                             /*              */
        char            wk5[14];                            /*              *///FFFFA850-FFFFA840-2
        union {                                             /* EEPWE0       *///FFFFA850
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned char KEY           : 8;            /*    KEY       */
                unsigned char               : 4;            /*              */
                unsigned char DBWE0         : 4;            /*    DBWE0     */
            }           BIT;                                /*              */
        }               EEPWE0;                             /*              */
        char            wk6[2];                             /*              *///FFFFA854-FFFFA850-2
        union {                                             /* FCURAME      *///FFFFA854
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned char KEY           : 8;            /*    KEY       */
                unsigned char               : 7;            /*              */
                unsigned char FCRME         : 1;            /*    FCRME     */
            }           BIT;                                /*              */
        }               FCURAME;                            /*              */
        char            wk7[170];                           /*              *///FFFFA900-FFFFA854-2
        union {                                             /* FSTATR0      *///FFFFA900
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char FRDY          : 1;            /*    FRDY      */
                unsigned char ILGERR        : 1;            /*    ILGERR    */
                unsigned char ERSERR        : 1;            /*    ERSERR    */
                unsigned char PRGERR        : 1;            /*    PRGERR    */
                unsigned char SUSRDY        : 1;            /*    SUSRDY    */
                unsigned char               : 1;            /*              */
                unsigned char ERSSPD        : 1;            /*    ERSSPD    */
                unsigned char PRGSPD        : 1;            /*    PRGSPD    */
            }           BIT;                                /*              */
        }               FSTATR0;                            /*              */
        union {                                             /* FSTATR1      *///FFFFA901
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char FCUERR        : 1;            /*    FCUERR    */
                unsigned char               : 2;            /*              */
                unsigned char FLOCKST       : 1;            /*    FLOCKST   */
                unsigned char               : 2;            /*              */
                unsigned char FRDTCT        : 1;            /*    FRDTCT    */
                unsigned char FRCRCT        : 1;            /*    FRCRCT    */
            }           BIT;                                /*              */
        }               FSTATR1;                            /*              */
        union {                                             /* FENTRYR      *///FFFFA902
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned char FKEY          : 8;            /*    FKEY      */
                unsigned char FENTRYD       : 1;            /*    FENTRYD   */
                unsigned char               : 6;            /*              */
                unsigned char FENTRY0       : 1;            /*    FENTRY0   */
            }           BIT;                                /*              */
        }               FENTRYR;                            /*              */
        union {                                             /* FPROTR       *///FFFFA904
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned char FPKEY         : 8;            /*    FPKEY     */
                unsigned char               : 7;            /*              */
                unsigned char FPROTCN       : 1;            /*    FPROTCN   */
            }           BIT;                                /*              */
        }               FPROTR;                             /*              */
        union {                                             /* FRESETR      *///FFFFA906
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned char FPKEY         : 8;            /*    FPKEY     */
                unsigned char               : 7;            /*              */
                unsigned char FRESET        : 1;            /*    FRESET    */
            }           BIT;                                /*              */
        }               FRESETR;                            /*              */
        char            wk8[2];                             /*              *///FFFFA90A-FFFFA906-2
        union {                                             /* FCMDR        *///FFFFA90A
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned char CMDR          : 8;            /*    CMDR      */
                unsigned char PCMDR         : 8;            /*    PCMDR     */
            }           BIT;                                /*              */
        }               FCMDR;                              /*              */
        union {                                             /* FRAMECCR     *///FFFFA90C
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 7;            /*              */
                unsigned char FRDCLE        : 1;            /*    FRDCLE    */
                unsigned char FRCCLE        : 1;            /*    FRCCLE    */
            }           BIT;                                /*              */
        }               FRAMECCR;                           /*              */
        char            wk9[10];                            /*              *///FFFFA918-FFFFA90C-2
        union {                                             /* FCPSR        *///FFFFA918
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 8;            /*              */
                unsigned char               : 7;            /*              */
                unsigned char ESUSPMD       : 1;            /*    ESUSPMD   */
            }           BIT;                                /*              */
        }               FCPSR;                              /*              */
        union {                                             /* EEPBCCNT     *///FFFFA91A
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short              : 3;            /*              */
                unsigned short BCADR        :10;            /*    BCADR     */
                unsigned short              : 2;            /*              */
                unsigned short BCSIZE       : 1;            /*    BCSIZE    */
            }           BIT;                                /*              */
        }               EEPBCCNT;                           /*              */
        union {                                             /* FPESTAT      *///FFFFA91C
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 8;            /*              */
                unsigned char PEERRST       : 8;            /*    PEERRST   */
            }           BIT;                                /*              */
        }               FPESTAT;                            /*              */
        union {                                             /* EEPBCSTAT    *///FFFFA91E
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 8;            /*              */
                unsigned char               : 7;            /*              */
                unsigned char BCST          : 1;            /*    BCST      */
            }           BIT;                                /*              */
        }               EEPBCSTAT;                          /*              */
};                                                          /*              */
struct st_romccr {                                          /* struct ROMCCR*/
        union {                                             /* RCCR         *///FFFC1400
            unsigned int    LONG;                           /*  Long Access */
            struct {                                        /*  Bit Access  */
                unsigned int                :28;            /*              */
                unsigned int RCF            : 1;            /*    RCF       */
                unsigned int                : 3;            /*              */
            }           BIT;                                /*              */
        }               RCCR;                               /*              */
};                                                          /*              */
struct st_stb {                                             /* struct STB   */
        union {                                             /* STBCR        *///FFFE0014
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char STBY          : 1;            /*    STBY      */
            }           BIT;                                /*              */
        }               CR;                                 /*              */
        char            wk1[3];                             /*              *///FFFE0018-FFFE0014-1
        union {                                             /* STBCR2       *///FFFE0018
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char _HUDI         : 1;            /*    H-UDI     */
                unsigned char _UBC          : 1;            /*    UBC       */
                unsigned char _DMAC         : 1;            /*    DMAC      */
                unsigned char               : 3;            /*              */
                unsigned char _DTC          : 1;            /*    DTC       */
            }           BIT;                                /*              */
        }               CR2;                                /*              */
        char            wk2[1007];                          /*              *///FFFE0408-FFFE0018-1
        union {                                             /* STBCR3       *///FFFE0408
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char HIZ           : 1;            /*    HIZ       */
                unsigned char _MTU2S        : 1;            /*    MTU2S     */
                unsigned char _MTU2         : 1;            /*    MTU2      */
                unsigned char _POE2         : 1;            /*    POE2      */
                unsigned char _IIC3         : 1;            /*    IIC3      */
                unsigned char _ADC0         : 1;            /*    ADC0      */
                unsigned char               : 1;            /*              */
                unsigned char _FLASH        : 1;            /*    FLASH     */
            }           BIT;                                /*              */
        }               CR3;                                /*              */
        char            wk3[3];                             /*              *///FFFE040C-FFFE0408-1
        union {                                             /* STBCR4       *///FFFE040C
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 3;            /*              */
                unsigned char _SCIF3        : 1;            /*    SCIF3     */
                unsigned char               : 1;            /*              */
                unsigned char _CMT          : 1;            /*    CMT       */
                unsigned char               : 1;            /*              */
                unsigned char _ETHER        : 1;            /*    ETHER     */
            }           BIT;                                /*              */
        }               CR4;                                /*              */
        char            wk4[11];                            /*              *///FFFE0418-FFFE040C-1
        union {                                             /* STBCR5       *///FFFE0418
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char _SCI0         : 1;            /*    SCI0      */
                unsigned char _SCI1         : 1;            /*    SCI1      */
                unsigned char _SCI2         : 1;            /*    SCI2      */
                unsigned char               : 1;            /*              */
                unsigned char _SCI4         : 1;            /*    SCI4      */
                unsigned char _ADC1         : 1;            /*    ADC1      */
                unsigned char               : 1;            /*              */
                unsigned char _RSPI         : 1;            /*    RSPI      */
            }           BIT;                                /*              */
        }               CR5;                                /*              */
        char            wk5[3];                             /*              *///FFFE041C-FFFE0418-1
        union {                                             /* STBCR6       *///FFFE041C
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char USBSEL        : 1;            /*    USBSEL    */
                unsigned char _USB          : 1;            /*    USB       */
                unsigned char USBCLK        : 1;            /*    USBCLK    */
                unsigned char _RCAN         : 1;            /*    RCAN      */
            }           BIT;                                /*              */
        }               CR6;                                /*              */
};                                                          /*              */
struct st_sys {                                             /* struct SYS   */
        union {                                             /* SYSCR1       *///FFFE0402
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 4;            /*              */
                unsigned char RAME3         : 1;            /*    RAME3     */
                unsigned char RAME2         : 1;            /*    RAME2     */
                unsigned char RAME1         : 1;            /*    RAME1     */
                unsigned char RAME0         : 1;            /*    RAME0     */
            }           BIT;                                /*              */
        }               CR1;                                /*              */
        char            wk1[1];                             /*              *///FFFE0404-FFFE0402-1
        union {                                             /* SYSCR2       *///FFFE0404
            unsigned char BYTE;                             /*  Byte Access */
            struct {                                        /*  Bit Access  */
                unsigned char               : 4;            /*              */
                unsigned char RAMWE3        : 1;            /*    RAMWE3    */
                unsigned char RAMWE2        : 1;            /*    RAMWE2    */
                unsigned char RAMWE1        : 1;            /*    RAMWE1    */
                unsigned char RAMWE0        : 1;            /*    RAMWE0    */
            }           BIT;                                /*              */
        }               CR2;                                /*              */
};                                                          /*              */
struct st_hudi {                                            /* struct H-UDI */
        union {                                             /* SDIR         *///FFFE2000
            unsigned short WORD;                            /*  Word Access */
            struct {                                        /*  Bit Access  */
                unsigned short TI           : 4;            /*    TI        */
            }           BIT;                                /*              */
        }               SDIR;                               /*              */
};                                                          /*              */

#define CPG    (*(volatile struct st_cpg    *)0xFFFE0010)   /* CPG    Address*/
#define INTC   (*(volatile struct st_intc   *)0xFFFE0800)   /* INTC   Address*/
#define UBC    (*(volatile struct st_ubc    *)0xFFFC04C0)   /* UBC    Address*/
#define UBC0   (*(volatile struct st_ubc0   *)0xFFFC0400)   /* UBC0   Address*/
#define UBC1   (*(volatile struct st_ubc0   *)0xFFFC0410)   /* UBC1   Address*/
#define UBC2   (*(volatile struct st_ubc2   *)0xFFFC0420)   /* UBC2   Address*/
#define UBC3   (*(volatile struct st_ubc2   *)0xFFFC0430)   /* UBC3   Address*/
#define DTC    (*(volatile struct st_dtc    *)0xFFFE6000)   /* DTC    Address*/
#define BSC    (*(volatile struct st_bsc    *)0xFFFC0000)   /* BSC    Address*/
#define DMAC   (*(volatile struct st_dmac   *)0xFFFE1200)   /* DMAC   Address*/
#define DMAC0  (*(volatile struct st_dmac0  *)0xFFFE1000)   /* DMAC0  Address*/
#define DMAC1  (*(volatile struct st_dmac0  *)0xFFFE1010)   /* DMAC1  Address*/
#define DMAC2  (*(volatile struct st_dmac2  *)0xFFFE1020)   /* DMAC2  Address*/
#define DMAC3  (*(volatile struct st_dmac2  *)0xFFFE1030)   /* DMAC3  Address*/
#define DMAC4  (*(volatile struct st_dmac4  *)0xFFFE1040)   /* DMAC4  Address*/
#define DMAC5  (*(volatile struct st_dmac4  *)0xFFFE1050)   /* DMAC5  Address*/
#define DMAC6  (*(volatile struct st_dmac4  *)0xFFFE1060)   /* DMAC6  Address*/
#define DMAC7  (*(volatile struct st_dmac4  *)0xFFFE1070)   /* DMAC7  Address*/
#define MTU2   (*(volatile struct st_mtu2   *)0xFFFE420A)   /* MTU2   Address*/
#define MTU20  (*(volatile struct st_mtu20  *)0xFFFE4300)   /* MTU20  Address*/
#define MTU21  (*(volatile struct st_mtu21  *)0xFFFE4380)   /* MTU21  Address*/
#define MTU22  (*(volatile struct st_mtu22  *)0xFFFE4000)   /* MTU22  Address*/
#define MTU23  (*(volatile struct st_mtu23  *)0xFFFE4200)   /* MTU23  Address*/
#define MTU24  (*(volatile struct st_mtu24  *)0xFFFE4200)   /* MTU24  Address*/
#define MTU25  (*(volatile struct st_mtu25  *)0xFFFE4080)   /* MTU25  Address*/
#define MTU2S  (*(volatile struct st_mtu2s  *)0xFFFE4A0A)   /* MTU2S  Address*/
#define MTU2S3 (*(volatile struct st_mtu23  *)0xFFFE4A00)   /* MTU2S3 Address*/
#define MTU2S4 (*(volatile struct st_mtu24  *)0xFFFE4A00)   /* MTU2S4 Address*/
#define MTU2S5 (*(volatile struct st_mtu25  *)0xFFFE4880)   /* MTU2S5 Address*/
#define POE2   (*(volatile struct st_poe2   *)0xFFFE5000)   /* POE    Address*/
#define CMT    (*(volatile struct st_cmt    *)0xFFFEC000)   /* CMT    Address*/
#define CMT0   (*(volatile struct st_cmt0   *)0xFFFEC002)   /* CMT0   Address*/
#define CMT1   (*(volatile struct st_cmt0   *)0xFFFEC008)   /* CMT1   Address*/
#define WDT    (*(volatile union  un_wdt    *)0xFFFE0000)   /* WDT    Address*/
#define SCI0   (*(volatile struct st_sci    *)0xFFFF8000)   /* SCI0   Address*/
#define SCI1   (*(volatile struct st_sci    *)0xFFFF8800)   /* SCI1   Address*/
#define SCI2   (*(volatile struct st_sci    *)0xFFFF9000)   /* SCI2   Address*/
#define SCI4   (*(volatile struct st_sci    *)0xFFFFA000)   /* SCI4   Address*/
#define SCIF3  (*(volatile struct st_scif   *)0xFFFE9800)   /* SCIF3  Address*/
#define RSPI   (*(volatile struct st_rspi   *)0xFFFFB000)   /* RSPI   Address*/
#define IIC3   (*(volatile struct st_iic3   *)0xFFFEE000)   /* IIC3   Address*/
#define ADC0   (*(volatile struct st_adc0   *)0xFFFFE800)   /* ADC0   Address*/
#define ADC1   (*(volatile struct st_adc1   *)0xFFFFEC00)   /* ADC1   Address*/
#define RCANET (*(volatile struct st_rcanet *)0xFFFFD000)   /* RCAN   Address*/
#define PFC    (*(volatile struct st_pfc    *)0xFFFE3804)   /* PFC    Address*/
#define PA     (*(volatile struct st_pa     *)0xFFFE3800)   /* PA     Address*/
#define PB     (*(volatile struct st_pb     *)0xFFFE3880)   /* PB     Address*/
#define PC     (*(volatile struct st_pc     *)0xFFFE3900)   /* PC     Address*/
#define PD     (*(volatile struct st_pd     *)0xFFFE3980)   /* PD     Address*/
#define PE     (*(volatile struct st_pe     *)0xFFFE3A00)   /* PE     Address*/
#define PF     (*(volatile struct st_pf     *)0xFFFE3A80)   /* PF     Address*/
#define USB    (*(volatile struct st_usb    *)0xFFFE7000)   /* USB    Address*/
#define EtherC (*(volatile struct st_etherc *)0xFFFC3100)   /* EtherC Address*/
#define EDMAC  (*(volatile struct st_edmac  *)0xFFFC3000)   /* EDMAC  Address*/
#define FLD    (*(volatile struct st_fld    *)0xFFFFA800)   /* FLD    Address*/
#define ROMCCR (*(volatile struct st_romccr *)0xFFFC1400)   /* ROMCCR Address*/
#define STB    (*(volatile struct st_stb    *)0xFFFE0014)   /* STB    Address*/
#define SYS    (*(volatile struct st_sys    *)0xFFFE0402)   /* SYS    Address*/
#define HUDI   (*(volatile struct st_hudi   *)0xFFFE2000)   /* H-UDI  Address*/

#endif      /* _IODEFINE_H_ */

/* End of File */
