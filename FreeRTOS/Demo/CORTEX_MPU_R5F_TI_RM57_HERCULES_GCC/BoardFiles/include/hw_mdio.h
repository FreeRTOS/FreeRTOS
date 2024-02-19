/*
 * hw_mdio.h
 */

/*
 * Copyright (C) 2009-2018 Texas Instruments Incorporated - www.ti.com
 *
 *
 *  Redistribution and use in source and binary forms, with or without
 *  modification, are permitted provided that the following conditions
 *  are met:
 *
 *    Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 *    Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the
 *    distribution.
 *
 *    Neither the name of Texas Instruments Incorporated nor the names of
 *    its contributors may be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 *  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 *  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 *  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 *  A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 *  OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 *  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 *  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 *  DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 *  THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 *  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 *  OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *
 */

#ifndef _HW_MDIO_H_
#define _HW_MDIO_H_

/* USER CODE BEGIN (0) */
/* USER CODE END */

#ifdef __cplusplus
extern "C" {
#endif

/* USER CODE BEGIN (1) */
/* USER CODE END */

#define MDIO_BASE                               ( 0xFCF78900U )

#define MDIO_REVID                              ( 0x0U )
#define MDIO_CONTROL                            ( 0x4U )
#define MDIO_ALIVE                              ( 0x8U )
#define MDIO_LINK                               ( 0xCU )
#define MDIO_LINKINTRAW                         ( 0x10U )
#define MDIO_LINKINTMASKED                      ( 0x14U )
#define MDIO_USERINTRAW                         ( 0x20U )
#define MDIO_USERINTMASKED                      ( 0x24U )
#define MDIO_USERINTMASKSET                     ( 0x28U )
#define MDIO_USERINTMASKCLEAR                   ( 0x2CU )
#define MDIO_USERACCESS0                        ( 0x80U )
#define MDIO_USERPHYSEL0                        ( 0x84U )
#define MDIO_USERACCESS1                        ( 0x88U )
#define MDIO_USERPHYSEL1                        ( 0x8CU )

/**************************************************************************\
* Field Definition Macros
\**************************************************************************/

/* REVID */

#define MDIO_REVID_REV                          ( 0xFFFFFFFFU )
#define MDIO_REVID_REV_SHIFT                    ( 0x00000000U )

/* CONTROL */

#define MDIO_CONTROL_IDLE                       ( 0x80000000U )
#define MDIO_CONTROL_IDLE_SHIFT                 ( 0x0000001FU )
/*----IDLE Tokens----*/
#define MDIO_CONTROL_IDLE_NO                    ( 0x00000000U )
#define MDIO_CONTROL_IDLE_YES                   ( 0x00000001U )

#define MDIO_CONTROL_ENABLE                     ( 0x40000000U )
#define MDIO_CONTROL_ENABLE_SHIFT               ( 0x0000001EU )

#define MDIO_CONTROL_HIGHEST_USER_CHANNEL       ( 0x1F000000U )
#define MDIO_CONTROL_HIGHEST_USER_CHANNEL_SHIFT ( 0x00000018U )

#define MDIO_CONTROL_PREAMBLE                   ( 0x00100000U )
#define MDIO_CONTROL_PREAMBLE_SHIFT             ( 0x00000014U )
/*----PREAMBLE Tokens----*/

#define MDIO_CONTROL_FAULT                      ( 0x00080000U )
#define MDIO_CONTROL_FAULT_SHIFT                ( 0x00000013U )

#define MDIO_CONTROL_FAULTENB                   ( 0x00040000U )
#define MDIO_CONTROL_FAULTENB_SHIFT             ( 0x00000012U )
/*----FAULTENB Tokens----*/

#define MDIO_CONTROL_CLKDIV                     ( 0x0000FFFFU )
#define MDIO_CONTROL_CLKDIV_SHIFT               ( 0x00000000U )
/*----CLKDIV Tokens----*/

/* ALIVE */

#define MDIO_ALIVE_REGVAL                       ( 0xFFFFFFFFU )
#define MDIO_ALIVE_REGVAL_SHIFT                 ( 0x00000000U )

/* LINK */

#define MDIO_LINK_REGVAL                        ( 0xFFFFFFFFU )
#define MDIO_LINK_REGVAL_SHIFT                  ( 0x00000000U )

/* LINKINTRAW */

#define MDIO_LINKINTRAW_USERPHY1                ( 0x00000002U )
#define MDIO_LINKINTRAW_USERPHY1_SHIFT          ( 0x00000001U )

#define MDIO_LINKINTRAW_USERPHY0                ( 0x00000001U )
#define MDIO_LINKINTRAW_USERPHY0_SHIFT          ( 0x00000000U )

/* LINKINTMASKED */

#define MDIO_LINKINTMASKED_USERPHY1             ( 0x00000002U )
#define MDIO_LINKINTMASKED_USERPHY1_SHIFT       ( 0x00000001U )

#define MDIO_LINKINTMASKED_USERPHY0             ( 0x00000001U )
#define MDIO_LINKINTMASKED_USERPHY0_SHIFT       ( 0x00000000U )

/* USERINTRAW */

#define MDIO_USERINTRAW_USERACCESS1             ( 0x00000002U )
#define MDIO_USERINTRAW_USERACCESS1_SHIFT       ( 0x00000001U )

#define MDIO_USERINTRAW_USERACCESS0             ( 0x00000001U )
#define MDIO_USERINTRAW_USERACCESS0_SHIFT       ( 0x00000000U )

/* USERINTMASKED */

#define MDIO_USERINTMASKED_USERACCESS1          ( 0x00000002U )
#define MDIO_USERINTMASKED_USERACCESS1_SHIFT    ( 0x00000001U )

#define MDIO_USERINTMASKED_USERACCESS0          ( 0x00000001U )
#define MDIO_USERINTMASKED_USERACCESS0_SHIFT    ( 0x00000000U )

/* USERINTMASKSET */

#define MDIO_USERINTMASKSET_USERACCESS1         ( 0x00000002U )
#define MDIO_USERINTMASKSET_USERACCESS1_SHIFT   ( 0x00000001U )

#define MDIO_USERINTMASKSET_USERACCESS0         ( 0x00000001U )
#define MDIO_USERINTMASKSET_USERACCESS0_SHIFT   ( 0x00000000U )

/* USERINTMASKCLEAR */

#define MDIO_USERINTMASKCLEAR_USERACCESS1       ( 0x00000002U )
#define MDIO_USERINTMASKCLEAR_USERACCESS1_SHIFT ( 0x00000001U )

#define MDIO_USERINTMASKCLEAR_USERACCESS0       ( 0x00000001U )
#define MDIO_USERINTMASKCLEAR_USERACCESS0_SHIFT ( 0x00000000U )

/* USERACCESS0 */

#define MDIO_USERACCESS0_GO                     ( 0x80000000U )
#define MDIO_USERACCESS0_GO_SHIFT               ( 0x0000001FU )

#define MDIO_USERACCESS0_WRITE                  ( 0x40000000U )
#define MDIO_USERACCESS0_READ                   ( 0x00000000U )
#define MDIO_USERACCESS0_WRITE_SHIFT            ( 0x0000001EU )

#define MDIO_USERACCESS0_ACK                    ( 0x20000000U )
#define MDIO_USERACCESS0_ACK_SHIFT              ( 0x0000001DU )

#define MDIO_USERACCESS0_REGADR                 ( 0x03E00000U )
#define MDIO_USERACCESS0_REGADR_SHIFT           ( 0x00000015U )

#define MDIO_USERACCESS0_PHYADR                 ( 0x001F0000U )
#define MDIO_USERACCESS0_PHYADR_SHIFT           ( 0x00000010U )

#define MDIO_USERACCESS0_DATA                   ( 0x0000FFFFU )
#define MDIO_USERACCESS0_DATA_SHIFT             ( 0x00000000U )

/* USERPHYSEL0 */

#define MDIO_USERPHYSEL0_LINKSEL                ( 0x00000080U )
#define MDIO_USERPHYSEL0_LINKSEL_SHIFT          ( 0x00000007U )

#define MDIO_USERPHYSEL0_LINKINTENB             ( 0x00000040U )
#define MDIO_USERPHYSEL0_LINKINTENB_SHIFT       ( 0x00000006U )

#define MDIO_USERPHYSEL0_PHYADRMON              ( 0x0000001FU )
#define MDIO_USERPHYSEL0_PHYADRMON_SHIFT        ( 0x00000000U )

/* USERACCESS1 */

#define MDIO_USERACCESS1_GO                     ( 0x80000000U )
#define MDIO_USERACCESS1_GO_SHIFT               ( 0x0000001FU )

#define MDIO_USERACCESS1_WRITE                  ( 0x40000000U )
#define MDIO_USERACCESS1_WRITE_SHIFT            ( 0x0000001EU )

#define MDIO_USERACCESS1_ACK                    ( 0x20000000U )
#define MDIO_USERACCESS1_ACK_SHIFT              ( 0x0000001DU )

#define MDIO_USERACCESS1_REGADR                 ( 0x03E00000U )
#define MDIO_USERACCESS1_REGADR_SHIFT           ( 0x00000015U )

#define MDIO_USERACCESS1_PHYADR                 ( 0x001F0000U )
#define MDIO_USERACCESS1_PHYADR_SHIFT           ( 0x00000010U )

#define MDIO_USERACCESS1_DATA                   ( 0x0000FFFFU )
#define MDIO_USERACCESS1_DATA_SHIFT             ( 0x00000000U )

/* USERPHYSEL1 */

#define MDIO_USERPHYSEL1_LINKSEL                ( 0x00000080U )
#define MDIO_USERPHYSEL1_LINKSEL_SHIFT          ( 0x00000007U )

#define MDIO_USERPHYSEL1_LINKINTENB             ( 0x00000040U )
#define MDIO_USERPHYSEL1_LINKINTENB_SHIFT       ( 0x00000006U )

#define MDIO_USERPHYSEL1_PHYADRMON              ( 0x0000001FU )
#define MDIO_USERPHYSEL1_PHYADRMON_SHIFT        ( 0x00000000U )

/* USER CODE BEGIN (2) */
/* USER CODE END */

#ifdef __cplusplus
}
#endif

#endif
