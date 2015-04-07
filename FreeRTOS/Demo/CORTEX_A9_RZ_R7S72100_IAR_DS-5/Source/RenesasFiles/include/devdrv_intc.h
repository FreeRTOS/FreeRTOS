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
/******************************************************************************
* File Name    : devdrv_intc.h
* $Rev: 17531 $
* $Date:: 2013-04-10 12:58:44 +0100#$
* Description  : Aragon Sample Program - INTC device driver header
******************************************************************************/
#ifndef _DEVDRV_INTC_H_
#define _DEVDRV_INTC_H_

/******************************************************************************
Includes   <System Includes> , "Project Includes"
******************************************************************************/


/******************************************************************************
Typedef definitions
******************************************************************************/


/******************************************************************************
Macro definitions
******************************************************************************/
#define INTC_ID_TOTAL           (587)

#define INTC_ID_SW0             (0)
#define INTC_ID_SW1             (1)     /*                                    */
#define INTC_ID_SW2             (2)     /*                                    */
#define INTC_ID_SW3             (3)     /*                                    */
#define INTC_ID_SW4             (4)     /*                                    */
#define INTC_ID_SW5             (5)     /*                                    */
#define INTC_ID_SW6             (6)     /*                                    */
#define INTC_ID_SW7             (7)     /*                                    */
#define INTC_ID_SW8             (8)     /*                                    */
#define INTC_ID_SW9             (9)     /*                                    */
#define INTC_ID_SW10            (10)    /*                                    */
#define INTC_ID_SW11            (11)    /*                                    */
#define INTC_ID_SW12            (12)    /*                                    */
#define INTC_ID_SW13            (13)    /*                                    */
#define INTC_ID_SW14            (14)    /*                                    */
#define INTC_ID_SW15            (15)    /*                                    */
#define INTC_ID_PMUIRQ0         (16)    /* CPU                                */
#define INTC_ID_COMMRX0         (17)    /*                                    */
#define INTC_ID_COMMTX0         (18)    /*                                    */
#define INTC_ID_CTIIRQ0         (19)    /*                                    */
#define INTC_ID_IRQ0            (32)    /* IRQ                                */
#define INTC_ID_IRQ1            (33)    /*                                    */
#define INTC_ID_IRQ2            (34)    /*                                    */
#define INTC_ID_IRQ3            (35)    /*                                    */
#define INTC_ID_IRQ4            (36)    /*                                    */
#define INTC_ID_IRQ5            (37)    /*                                    */
#define INTC_ID_IRQ6            (38)    /*                                    */
#define INTC_ID_IRQ7            (39)    /*                                    */
#define INTC_ID_PL310ERR        (40)
#define INTC_ID_DMAINT0         (41)
#define INTC_ID_DMAINT1         (42)    /*                                    */
#define INTC_ID_DMAINT2         (43)    /*                                    */
#define INTC_ID_DMAINT3         (44)    /*                                    */
#define INTC_ID_DMAINT4         (45)    /*                                    */
#define INTC_ID_DMAINT5         (46)    /*                                    */
#define INTC_ID_DMAINT6         (47)    /*                                    */
#define INTC_ID_DMAINT7         (48)    /*                                    */
#define INTC_ID_DMAINT8         (49)    /*                                    */
#define INTC_ID_DMAINT9         (50)    /*                                    */
#define INTC_ID_DMAINT10        (51)    /*                                    */
#define INTC_ID_DMAINT11        (52)    /*                                    */
#define INTC_ID_DMAINT12        (53)    /*                                    */
#define INTC_ID_DMAINT13        (54)    /*                                    */
#define INTC_ID_DMAINT14        (55)    /*                                    */
#define INTC_ID_DMAINT15        (56)    /*                                    */
#define INTC_ID_DMAERR          (57)    /*                                    */
#define INTC_ID_USBI0           (73)
#define INTC_ID_USBI1           (74)    /*                                    */
#define INTC_ID_S0_VI_VSYNC0    (75)
#define INTC_ID_S0_LO_VSYNC0    (76)    /*                                    */
#define INTC_ID_S0_VSYNCERR0    (77)    /*                                    */
#define INTC_ID_GR3_VLINE0      (78)    /*                                    */
#define INTC_ID_S0_VFIELD0      (79)    /*                                    */
#define INTC_ID_IV1_VBUFERR0    (80)    /*                                    */
#define INTC_ID_IV3_VBUFERR0    (81)    /*                                    */
#define INTC_ID_IV5_VBUFERR0    (82)    /*                                    */
#define INTC_ID_IV6_VBUFERR0    (83)    /*                                    */
#define INTC_ID_S0_WLINE0       (84)    /*                                    */
#define INTC_ID_S1_VI_VSYNC0    (85)    /*                                    */
#define INTC_ID_S1_LO_VSYNC0    (86)    /*                                    */
#define INTC_ID_S1_VSYNCERR0    (87)    /*                                    */
#define INTC_ID_S1_VFIELD0      (88)    /*                                    */
#define INTC_ID_IV2_VBUFERR0    (89)    /*                                    */
#define INTC_ID_IV4_VBUFERR0    (90)    /*                                    */
#define INTC_ID_S1_WLINE0       (91)    /*                                    */
#define INTC_ID_OIR_VI_VSYNC0   (92)    /*                                    */
#define INTC_ID_OIR_LO_VSYNC0   (93)    /*                                    */
#define INTC_ID_OIR_VSYNCERR0   (94)    /*                                    */
#define INTC_ID_OIR_VFIELD0     (95)    /*                                    */
#define INTC_ID_IV7_VBUFERR0    (96)    /*                                    */
#define INTC_ID_IV8_VBUFERR0    (97)    /*                                    */
#define INTC_ID_OIR_WLINE0      (98)    /*                                    */
#define INTC_ID_S0_VI_VSYNC1    (99)    /*                                    */
#define INTC_ID_S0_LO_VSYNC1    (100)   /*                                    */
#define INTC_ID_S0_VSYNCERR1    (101)   /*                                    */
#define INTC_ID_GR3_VLINE1      (102)   /*                                    */
#define INTC_ID_S0_VFIELD1      (103)   /*                                    */
#define INTC_ID_IV1_VBUFERR1    (104)   /*                                    */
#define INTC_ID_IV3_VBUFERR1    (105)   /*                                    */
#define INTC_ID_IV5_VBUFERR1    (106)   /*                                    */
#define INTC_ID_IV6_VBUFERR1    (107)   /*                                    */
#define INTC_ID_S0_WLINE1       (108)   /*                                    */
#define INTC_ID_S1_VI_VSYNC1    (109)   /*                                    */
#define INTC_ID_S1_LO_VSYNC1    (110)   /*                                    */
#define INTC_ID_S1_VSYNCERR1    (111)   /*                                    */
#define INTC_ID_S1_VFIELD1      (112)   /*                                    */
#define INTC_ID_IV2_VBUFERR1    (113)   /*                                    */
#define INTC_ID_IV4_VBUFERR1    (114)   /*                                    */
#define INTC_ID_S1_WLINE1       (115)   /*                                    */
#define INTC_ID_OIR_VI_VSYNC1   (116)   /*                                    */
#define INTC_ID_OIR_LO_VSYNC1   (117)   /*                                    */
#define INTC_ID_OIR_VLINE1      (118)   /*                                    */
#define INTC_ID_OIR_VFIELD1     (119)   /*                                    */
#define INTC_ID_IV7_VBUFERR1    (120)   /*                                    */
#define INTC_ID_IV8_VBUFERR1    (121)   /*                                    */
#define INTC_ID_OIR_WLINE1      (122)   /*                                    */
#define INTC_ID_IMRDI           (123)
#define INTC_ID_IMR2I0          (124)   /*                                    */
#define INTC_ID_IMR2I1          (125)   /*                                    */
#define INTC_ID_JEDI            (126)
#define INTC_ID_JDTI            (127)   /*                                    */
#define INTC_ID_CMP0            (128)
#define INTC_ID_CMP1            (129)   /*                                    */
#define INTC_ID_INT0            (130)
#define INTC_ID_INT1            (131)   /*                                    */
#define INTC_ID_INT2            (132)   /*                                    */
#define INTC_ID_INT3            (133)   /*                                    */
#define INTC_ID_OSTMI0          (134)
#define INTC_ID_OSTMI1          (135)   /*                                    */
#define INTC_ID_CMI             (136)
#define INTC_ID_WTOUT           (137)   /*                                    */
#define INTC_ID_ITI             (138)
#define INTC_ID_TGI0A           (139)
#define INTC_ID_TGI0B           (140)   /*                                    */
#define INTC_ID_TGI0C           (141)   /*                                    */
#define INTC_ID_TGI0D           (142)   /*                                    */
#define INTC_ID_TGI0V           (143)   /*                                    */
#define INTC_ID_TGI0E           (144)   /*                                    */
#define INTC_ID_TGI0F           (145)   /*                                    */
#define INTC_ID_TGI1A           (146)   /*                                    */
#define INTC_ID_TGI1B           (147)   /*                                    */
#define INTC_ID_TGI1V           (148)   /*                                    */
#define INTC_ID_TGI1U           (149)   /*                                    */
#define INTC_ID_TGI2A           (150)   /*                                    */
#define INTC_ID_TGI2B           (151)   /*                                    */
#define INTC_ID_TGI2V           (152)   /*                                    */
#define INTC_ID_TGI2U           (153)   /*                                    */
#define INTC_ID_TGI3A           (154)   /*                                    */
#define INTC_ID_TGI3B           (155)   /*                                    */
#define INTC_ID_TGI3C           (156)   /*                                    */
#define INTC_ID_TGI3D           (157)   /*                                    */
#define INTC_ID_TGI3V           (158)   /*                                    */
#define INTC_ID_TGI4A           (159)   /*                                    */
#define INTC_ID_TGI4B           (160)   /*                                    */
#define INTC_ID_TGI4C           (161)   /*                                    */
#define INTC_ID_TGI4D           (162)   /*                                    */
#define INTC_ID_TGI4V           (163)   /*                                    */
#define INTC_ID_CMI1            (164)
#define INTC_ID_CMI2            (165)   /*                                    */
#define INTC_ID_SGDEI0          (166)
#define INTC_ID_SGDEI1          (167)   /*                                    */
#define INTC_ID_SGDEI2          (168)   /*                                    */
#define INTC_ID_SGDEI3          (169)   /*                                    */
#define INTC_ID_ADI             (170)
#define INTC_ID_ADWAR           (171)   /*                                    */
#define INTC_ID_SSII0           (172)
#define INTC_ID_SSIRXI0         (173)   /*                                    */
#define INTC_ID_SSITXI0         (174)   /*                                    */
#define INTC_ID_SSII1           (175)   /*                                    */
#define INTC_ID_SSIRXI1         (176)   /*                                    */
#define INTC_ID_SSITXI1         (177)   /*                                    */
#define INTC_ID_SSII2           (178)   /*                                    */
#define INTC_ID_SSIRTI2         (179)   /*                                    */
#define INTC_ID_SSII3           (180)   /*                                    */
#define INTC_ID_SSIRXI3         (181)   /*                                    */
#define INTC_ID_SSITXI3         (182)   /*                                    */
#define INTC_ID_SSII4           (183)   /*                                    */
#define INTC_ID_SSIRTI4         (184)   /*                                    */
#define INTC_ID_SSII5           (185)   /*                                    */
#define INTC_ID_SSIRXI5         (186)   /*                                    */
#define INTC_ID_SSITXI5         (187)   /*                                    */
#define INTC_ID_SPDIFI          (188)
#define INTC_ID_TEI0            (189)
#define INTC_ID_RI0             (190)   /*                                    */
#define INTC_ID_TI0             (191)   /*                                    */
#define INTC_ID_SPI0            (192)   /*                                    */
#define INTC_ID_STI0            (193)   /*                                    */
#define INTC_ID_NAKI0           (194)   /*                                    */
#define INTC_ID_ALI0            (195)   /*                                    */
#define INTC_ID_TMOI0           (196)   /*                                    */
#define INTC_ID_TEI1            (197)   /*                                    */
#define INTC_ID_RI1             (198)   /*                                    */
#define INTC_ID_TI1             (199)   /*                                    */
#define INTC_ID_SPI1            (200)   /*                                    */
#define INTC_ID_STI1            (201)   /*                                    */
#define INTC_ID_NAKI1           (202)   /*                                    */
#define INTC_ID_ALI1            (203)   /*                                    */
#define INTC_ID_TMOI1           (204)   /*                                    */
#define INTC_ID_TEI2            (205)   /*                                    */
#define INTC_ID_RI2             (206)   /*                                    */
#define INTC_ID_TI2             (207)   /*                                    */
#define INTC_ID_SPI2            (208)   /*                                    */
#define INTC_ID_STI2            (209)   /*                                    */
#define INTC_ID_NAKI2           (210)   /*                                    */
#define INTC_ID_ALI2            (211)   /*                                    */
#define INTC_ID_TMOI2           (212)   /*                                    */
#define INTC_ID_TEI3            (213)   /*                                    */
#define INTC_ID_RI3             (214)   /*                                    */
#define INTC_ID_TI3             (215)   /*                                    */
#define INTC_ID_SPI3            (216)   /*                                    */
#define INTC_ID_STI3            (217)   /*                                    */
#define INTC_ID_NAKI3           (218)   /*                                    */
#define INTC_ID_ALI3            (219)   /*                                    */
#define INTC_ID_TMOI3           (220)   /*                                    */
#define INTC_ID_BRI0            (221)
#define INTC_ID_ERI0            (222)   /*                                    */
#define INTC_ID_RXI0            (223)   /*                                    */
#define INTC_ID_TXI0            (224)   /*                                    */
#define INTC_ID_BRI1            (225)   /*                                    */
#define INTC_ID_ERI1            (226)   /*                                    */
#define INTC_ID_RXI1            (227)   /*                                    */
#define INTC_ID_TXI1            (228)   /*                                    */
#define INTC_ID_BRI2            (229)   /*                                    */
#define INTC_ID_ERI2            (230)   /*                                    */
#define INTC_ID_RXI2            (231)   /*                                    */
#define INTC_ID_TXI2            (232)   /*                                    */
#define INTC_ID_BRI3            (233)   /*                                    */
#define INTC_ID_ERI3            (234)   /*                                    */
#define INTC_ID_RXI3            (235)   /*                                    */
#define INTC_ID_TXI3            (236)   /*                                    */
#define INTC_ID_BRI4            (237)   /*                                    */
#define INTC_ID_ERI4            (238)   /*                                    */
#define INTC_ID_RXI4            (239)   /*                                    */
#define INTC_ID_TXI4            (240)   /*                                    */
#define INTC_ID_BRI5            (241)   /*                                    */
#define INTC_ID_ERI5            (242)   /*                                    */
#define INTC_ID_RXI5            (243)   /*                                    */
#define INTC_ID_TXI5            (244)   /*                                    */
#define INTC_ID_BRI6            (245)   /*                                    */
#define INTC_ID_ERI6            (246)   /*                                    */
#define INTC_ID_RXI6            (247)   /*                                    */
#define INTC_ID_TXI6            (248)   /*                                    */
#define INTC_ID_BRI7            (249)   /*                                    */
#define INTC_ID_ERI7            (250)   /*                                    */
#define INTC_ID_RXI7            (251)   /*                                    */
#define INTC_ID_TXI7            (252)   /*                                    */
#define INTC_ID_GERI            (253)
#define INTC_ID_RFI             (254)   /*                                    */
#define INTC_ID_CFRXI0          (255)   /*                                    */
#define INTC_ID_CERI0           (256)   /*                                    */
#define INTC_ID_CTXI0           (257)   /*                                    */
#define INTC_ID_CFRXI1          (258)   /*                                    */
#define INTC_ID_CERI1           (259)   /*                                    */
#define INTC_ID_CTXI1           (260)   /*                                    */
#define INTC_ID_CFRXI2          (261)   /*                                    */
#define INTC_ID_CERI2           (262)   /*                                    */
#define INTC_ID_CTXI2           (263)   /*                                    */
#define INTC_ID_CFRXI3          (264)   /*                                    */
#define INTC_ID_CERI3           (265)   /*                                    */
#define INTC_ID_CTXI3           (266)   /*                                    */
#define INTC_ID_CFRXI4          (267)   /*                                    */
#define INTC_ID_CERI4           (268)   /*                                    */
#define INTC_ID_CTXI4           (269)   /*                                    */
#define INTC_ID_SPEI0           (270)
#define INTC_ID_SPRI0           (271)   /*                                    */
#define INTC_ID_SPTI0           (272)   /*                                    */
#define INTC_ID_SPEI1           (273)   /*                                    */
#define INTC_ID_SPRI1           (274)   /*                                    */
#define INTC_ID_SPTI1           (275)   /*                                    */
#define INTC_ID_SPEI2           (276)   /*                                    */
#define INTC_ID_SPRI2           (277)   /*                                    */
#define INTC_ID_SPTI2           (278)   /*                                    */
#define INTC_ID_SPEI3           (279)   /*                                    */
#define INTC_ID_SPRI3           (280)   /*                                    */
#define INTC_ID_SPTI3           (281)   /*                                    */
#define INTC_ID_SPEI4           (282)   /*                                    */
#define INTC_ID_SPRI4           (283)   /*                                    */
#define INTC_ID_SPTI4           (284)   /*                                    */
#define INTC_ID_IEBBTD          (285)
#define INTC_ID_IEBBTERR        (286)   /*                                    */
#define INTC_ID_IEBBTSTA        (287)   /*                                    */
#define INTC_ID_IEBBTV          (288)   /*                                    */
#define INTC_ID_ISY             (289)
#define INTC_ID_IERR            (290)   /*                                    */
#define INTC_ID_ITARG           (291)   /*                                    */
#define INTC_ID_ISEC            (292)   /*                                    */
#define INTC_ID_IBUF            (293)   /*                                    */
#define INTC_ID_IREADY          (294)   /*                                    */
#define INTC_ID_FLSTE           (295)
#define INTC_ID_FLTENDI         (296)   /*                                    */
#define INTC_ID_FLTREQ0I        (297)   /*                                    */
#define INTC_ID_FLTREQ1I        (298)   /*                                    */
#define INTC_ID_MMC0            (299)
#define INTC_ID_MMC1            (300)   /*                                    */
#define INTC_ID_MMC2            (301)   /*                                    */
#define INTC_ID_SDHI0_3         (302)
#define INTC_ID_SDHI0_0         (303)   /*                                    */
#define INTC_ID_SDHI0_1         (304)   /*                                    */
#define INTC_ID_SDHI1_3         (305)   /*                                    */
#define INTC_ID_SDHI1_0         (306)   /*                                    */
#define INTC_ID_SDHI1_1         (307)   /*                                    */
#define INTC_ID_ARM             (308)
#define INTC_ID_PRD             (309)   /*                                    */
#define INTC_ID_CUP             (310)   /*                                    */
#define INTC_ID_SCUAI0          (311)   /* SCUX                               */
#define INTC_ID_SCUAI1          (312)   /*                                    */
#define INTC_ID_SCUFDI0         (313)   /*                                    */
#define INTC_ID_SCUFDI1         (314)   /*                                    */
#define INTC_ID_SCUFDI2         (315)   /*                                    */
#define INTC_ID_SCUFDI3         (316)   /*                                    */
#define INTC_ID_SCUFUI0         (317)   /*                                    */
#define INTC_ID_SCUFUI1         (318)   /*                                    */
#define INTC_ID_SCUFUI2         (319)   /*                                    */
#define INTC_ID_SCUFUI3         (320)   /*                                    */
#define INTC_ID_SCUDVI0         (321)   /*                                    */
#define INTC_ID_SCUDVI1         (322)   /*                                    */
#define INTC_ID_SCUDVI2         (323)   /*                                    */
#define INTC_ID_SCUDVI3         (324)   /*                                    */
#define INTC_ID_MLBCI           (325)
#define INTC_ID_MLBSI           (326)   /*                                    */
#define INTC_ID_DRC0            (327)
#define INTC_ID_DRC1            (328)   /*                                    */
#define INTC_ID_LINI0_INT_T     (331)   /* Renesas LIN3                       */
#define INTC_ID_LINI0_INT_R     (332)   /*                                    */
#define INTC_ID_LINI0_INT_S     (333)   /*                                    */
#define INTC_ID_LINI0_INT_M     (334)   /*                                    */
#define INTC_ID_LINI1_INT_T     (335)   /*                                    */
#define INTC_ID_LINI1_INT_R     (336)   /*                                    */
#define INTC_ID_LINI1_INT_S     (337)   /*                                    */
#define INTC_ID_LINI1_INT_M     (338)   /*                                    */
#define INTC_ID_SCI_ERI0        (347)
#define INTC_ID_SCI_RXI0        (348)   /*                                    */
#define INTC_ID_SCI_TXI0        (349)   /*                                    */
#define INTC_ID_SCI_TEI0        (350)   /*                                    */
#define INTC_ID_SCI_ERI1        (351)   /*                                    */
#define INTC_ID_SCI_RXI1        (352)   /*                                    */
#define INTC_ID_SCI_TXI1        (353)   /*                                    */
#define INTC_ID_SCI_TEI1        (354)   /*                                    */
#define INTC_ID_ETHERI          (359)
#define INTC_ID_CEUI            (364)
#define INTC_ID_H2XMLB_ERRINT   (381)
#define INTC_ID_H2XIC1_ERRINT   (382)   /*                                    */
#define INTC_ID_X2HPERI1_ERRINT (383)   /*                                    */
#define INTC_ID_X2HPERI2_ERRINT (384)   /*                                    */
#define INTC_ID_X2HPERI34_ERRINT (385)  /*                                    */
#define INTC_ID_X2HPERI5_ERRINT (386)   /*                                    */
#define INTC_ID_X2HPERI67_ERRINT (387)  /*                                    */
#define INTC_ID_X2HDBGR_ERRINT  (388)   /*                                    */
#define INTC_ID_X2HBSC_ERRINT   (389)   /*                                    */
#define INTC_ID_X2HSPI1_ERRINT  (390)   /*                                    */
#define INTC_ID_X2HSPI2_ERRINT  (391)   /*                                    */
#define INTC_ID_PRRI            (392)   /*                                    */
#define INTC_ID_IFEI0           (393)
#define INTC_ID_OFFI0           (394)   /*                                    */
#define INTC_ID_PFVEI0          (395)   /*                                    */
#define INTC_ID_IFEI1           (396)   /*                                    */
#define INTC_ID_OFFI1           (397)   /*                                    */
#define INTC_ID_PFVEI1          (398)   /*                                    */
#define INTC_ID_TINT0           (416)
#define INTC_ID_TINT1           (417)   /*                                    */
#define INTC_ID_TINT2           (418)   /*                                    */
#define INTC_ID_TINT3           (419)   /*                                    */
#define INTC_ID_TINT4           (420)   /*                                    */
#define INTC_ID_TINT5           (421)   /*                                    */
#define INTC_ID_TINT6           (422)   /*                                    */
#define INTC_ID_TINT7           (423)   /*                                    */
#define INTC_ID_TINT8           (424)   /*                                    */
#define INTC_ID_TINT9           (425)   /*                                    */
#define INTC_ID_TINT10          (426)   /*                                    */
#define INTC_ID_TINT11          (427)   /*                                    */
#define INTC_ID_TINT12          (428)   /*                                    */
#define INTC_ID_TINT13          (429)   /*                                    */
#define INTC_ID_TINT14          (430)   /*                                    */
#define INTC_ID_TINT15          (431)   /*                                    */
#define INTC_ID_TINT16          (432)   /*                                    */
#define INTC_ID_TINT17          (433)   /*                                    */
#define INTC_ID_TINT18          (434)   /*                                    */
#define INTC_ID_TINT19          (435)   /*                                    */
#define INTC_ID_TINT20          (436)   /*                                    */
#define INTC_ID_TINT21          (437)   /*                                    */
#define INTC_ID_TINT22          (438)   /*                                    */
#define INTC_ID_TINT23          (439)   /*                                    */
#define INTC_ID_TINT24          (440)   /*                                    */
#define INTC_ID_TINT25          (441)   /*                                    */
#define INTC_ID_TINT26          (442)   /*                                    */
#define INTC_ID_TINT27          (443)   /*                                    */
#define INTC_ID_TINT28          (444)   /*                                    */
#define INTC_ID_TINT29          (445)   /*                                    */
#define INTC_ID_TINT30          (446)   /*                                    */
#define INTC_ID_TINT31          (447)   /*                                    */
#define INTC_ID_TINT32          (448)   /*                                    */
#define INTC_ID_TINT33          (449)   /*                                    */
#define INTC_ID_TINT34          (450)   /*                                    */
#define INTC_ID_TINT35          (451)   /*                                    */
#define INTC_ID_TINT36          (452)   /*                                    */
#define INTC_ID_TINT37          (453)   /*                                    */
#define INTC_ID_TINT38          (454)   /*                                    */
#define INTC_ID_TINT39          (455)   /*                                    */
#define INTC_ID_TINT40          (456)   /*                                    */
#define INTC_ID_TINT41          (457)   /*                                    */
#define INTC_ID_TINT42          (458)   /*                                    */
#define INTC_ID_TINT43          (459)   /*                                    */
#define INTC_ID_TINT44          (460)   /*                                    */
#define INTC_ID_TINT45          (461)   /*                                    */
#define INTC_ID_TINT46          (462)   /*                                    */
#define INTC_ID_TINT47          (463)   /*                                    */
#define INTC_ID_TINT48          (464)   /*                                    */
#define INTC_ID_TINT49          (465)   /*                                    */
#define INTC_ID_TINT50          (466)   /*                                    */
#define INTC_ID_TINT51          (467)   /*                                    */
#define INTC_ID_TINT52          (468)   /*                                    */
#define INTC_ID_TINT53          (469)   /*                                    */
#define INTC_ID_TINT54          (470)   /*                                    */
#define INTC_ID_TINT55          (471)   /*                                    */
#define INTC_ID_TINT56          (472)   /*                                    */
#define INTC_ID_TINT57          (473)   /*                                    */
#define INTC_ID_TINT58          (474)   /*                                    */
#define INTC_ID_TINT59          (475)   /*                                    */
#define INTC_ID_TINT60          (476)   /*                                    */
#define INTC_ID_TINT61          (477)   /*                                    */
#define INTC_ID_TINT62          (478)   /*                                    */
#define INTC_ID_TINT63          (479)   /*                                    */
#define INTC_ID_TINT64          (480)   /*                                    */
#define INTC_ID_TINT65          (481)   /*                                    */
#define INTC_ID_TINT66          (482)   /*                                    */
#define INTC_ID_TINT67          (483)   /*                                    */
#define INTC_ID_TINT68          (484)   /*                                    */
#define INTC_ID_TINT69          (485)   /*                                    */
#define INTC_ID_TINT70          (486)   /*                                    */
#define INTC_ID_TINT71          (487)   /*                                    */
#define INTC_ID_TINT72          (488)   /*                                    */
#define INTC_ID_TINT73          (489)   /*                                    */
#define INTC_ID_TINT74          (490)   /*                                    */
#define INTC_ID_TINT75          (491)   /*                                    */
#define INTC_ID_TINT76          (492)   /*                                    */
#define INTC_ID_TINT77          (493)   /*                                    */
#define INTC_ID_TINT78          (494)   /*                                    */
#define INTC_ID_TINT79          (495)   /*                                    */
#define INTC_ID_TINT80          (496)   /*                                    */
#define INTC_ID_TINT81          (497)   /*                                    */
#define INTC_ID_TINT82          (498)   /*                                    */
#define INTC_ID_TINT83          (499)   /*                                    */
#define INTC_ID_TINT84          (500)   /*                                    */
#define INTC_ID_TINT85          (501)   /*                                    */
#define INTC_ID_TINT86          (502)   /*                                    */
#define INTC_ID_TINT87          (503)   /*                                    */
#define INTC_ID_TINT88          (504)   /*                                    */
#define INTC_ID_TINT89          (505)   /*                                    */
#define INTC_ID_TINT90          (506)   /*                                    */
#define INTC_ID_TINT91          (507)   /*                                    */
#define INTC_ID_TINT92          (508)   /*                                    */
#define INTC_ID_TINT93          (509)   /*                                    */
#define INTC_ID_TINT94          (510)   /*                                    */
#define INTC_ID_TINT95          (511)   /*                                    */
#define INTC_ID_TINT96          (512)   /*                                    */
#define INTC_ID_TINT97          (513)   /*                                    */
#define INTC_ID_TINT98          (514)   /*                                    */
#define INTC_ID_TINT99          (515)   /*                                    */
#define INTC_ID_TINT100         (516)   /*                                    */
#define INTC_ID_TINT101         (517)   /*                                    */
#define INTC_ID_TINT102         (518)   /*                                    */
#define INTC_ID_TINT103         (519)   /*                                    */
#define INTC_ID_TINT104         (520)   /*                                    */
#define INTC_ID_TINT105         (521)   /*                                    */
#define INTC_ID_TINT106         (522)   /*                                    */
#define INTC_ID_TINT107         (523)   /*                                    */
#define INTC_ID_TINT108         (524)   /*                                    */
#define INTC_ID_TINT109         (525)   /*                                    */
#define INTC_ID_TINT110         (526)   /*                                    */
#define INTC_ID_TINT111         (527)   /*                                    */
#define INTC_ID_TINT112         (528)   /*                                    */
#define INTC_ID_TINT113         (529)   /*                                    */
#define INTC_ID_TINT114         (530)   /*                                    */
#define INTC_ID_TINT115         (531)   /*                                    */
#define INTC_ID_TINT116         (532)   /*                                    */
#define INTC_ID_TINT117         (533)   /*                                    */
#define INTC_ID_TINT118         (534)   /*                                    */
#define INTC_ID_TINT119         (535)   /*                                    */
#define INTC_ID_TINT120         (536)   /*                                    */
#define INTC_ID_TINT121         (537)   /*                                    */
#define INTC_ID_TINT122         (538)   /*                                    */
#define INTC_ID_TINT123         (539)   /*                                    */
#define INTC_ID_TINT124         (540)   /*                                    */
#define INTC_ID_TINT125         (541)   /*                                    */
#define INTC_ID_TINT126         (542)   /*                                    */
#define INTC_ID_TINT127         (543)   /*                                    */
#define INTC_ID_TINT128         (544)   /*                                    */
#define INTC_ID_TINT129         (545)   /*                                    */
#define INTC_ID_TINT130         (546)   /*                                    */
#define INTC_ID_TINT131         (547)   /*                                    */
#define INTC_ID_TINT132         (548)   /*                                    */
#define INTC_ID_TINT133         (549)   /*                                    */
#define INTC_ID_TINT134         (550)   /*                                    */
#define INTC_ID_TINT135         (551)   /*                                    */
#define INTC_ID_TINT136         (552)   /*                                    */
#define INTC_ID_TINT137         (553)   /*                                    */
#define INTC_ID_TINT138         (554)   /*                                    */
#define INTC_ID_TINT139         (555)   /*                                    */
#define INTC_ID_TINT140         (556)   /*                                    */
#define INTC_ID_TINT141         (557)   /*                                    */
#define INTC_ID_TINT142         (558)   /*                                    */
#define INTC_ID_TINT143         (559)   /*                                    */
#define INTC_ID_TINT144         (560)   /*                                    */
#define INTC_ID_TINT145         (561)   /*                                    */
#define INTC_ID_TINT146         (562)   /*                                    */
#define INTC_ID_TINT147         (563)   /*                                    */
#define INTC_ID_TINT148         (564)   /*                                    */
#define INTC_ID_TINT149         (565)   /*                                    */
#define INTC_ID_TINT150         (566)   /*                                    */
#define INTC_ID_TINT151         (567)   /*                                    */
#define INTC_ID_TINT152         (568)   /*                                    */
#define INTC_ID_TINT153         (569)   /*                                    */
#define INTC_ID_TINT154         (570)   /*                                    */
#define INTC_ID_TINT155         (571)   /*                                    */
#define INTC_ID_TINT156         (572)   /*                                    */
#define INTC_ID_TINT157         (573)   /*                                    */
#define INTC_ID_TINT158         (574)   /*                                    */
#define INTC_ID_TINT159         (575)   /*                                    */
#define INTC_ID_TINT160         (576)   /*                                    */
#define INTC_ID_TINT161         (577)   /*                                    */
#define INTC_ID_TINT162         (578)   /*                                    */
#define INTC_ID_TINT163         (579)   /*                                    */
#define INTC_ID_TINT164         (580)   /*                                    */
#define INTC_ID_TINT165         (581)   /*                                    */
#define INTC_ID_TINT166         (582)   /*                                    */
#define INTC_ID_TINT167         (583)   /*                                    */
#define INTC_ID_TINT168         (584)   /*                                    */
#define INTC_ID_TINT169         (585)   /*                                    */
#define INTC_ID_TINT170         (586)   /*                                    */

#define INTC_LEVEL_SENSITIVE    (0)
#define INTC_EDGE_TRIGGER       (1)


/******************************************************************************
Variable Externs
******************************************************************************/


/******************************************************************************
Functions Prototypes
******************************************************************************/
int32_t R_INTC_RegistIntFunc(uint16_t int_id, void (* func)(uint32_t int_sense));
void    R_INTC_Init(void);
int32_t R_INTC_Enable(uint16_t int_id);
int32_t R_INTC_Disable(uint16_t int_id);
int32_t R_INTC_SetPriority(uint16_t int_id, uint8_t priority);
int32_t R_INTC_SetMaskLevel(uint8_t mask_level);
void    R_INTC_GetMaskLevel(uint8_t * mask_level);

void    Userdef_INTC_RegistIntFunc(uint16_t int_id, void (* func)(uint32_t int_sense));
void    Userdef_INTC_UndefId(uint16_t int_id);
void    Userdef_INTC_HandlerExe(uint16_t int_id, uint32_t int_sense);
void    Userdef_FIQ_HandlerExe(void);

#endif  /* _DEVDRV_INTC_H_ */

/* End of File */
