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
* Copyright (C) 2014 Renesas Electronics Corporation. All rights reserved.
*******************************************************************************/
/*******************************************************************************
* File Name     : r_dtc_rx_config.h
* Description   : Configures the DTC drivers
********************************************************************************
* History : DD.MM.YYYY Version Description
*         : 15.01.2014 1.00    Initial revision
*         : 17.07.2014 2.00    Second  revision
*         : 12.11.2014 2.01    Added RX113.
*         : 30.01.2015 2.02    Added RX71M.
*         : 13.04.2015 2.03    Added RX231 and RX230.
*         : 24.12.2015 2.04    Added RX130, RX23T and RX24T.
*         :                    Modified #define name from "DTC_CFG_SHORT_ADDRRESS_MODE"
*         :                    to "DTC_CFG_SHORT_ADDRESS_MODE".
*         : 30.09.2016 2.05    Added RX65N.
*         :                    Added #define DTC_CFG_USE_SEQUENCE_TRANSFER.
*         : 31.03.2017 2.07    Added RX24U and RX24T-512KB.
*         : 31.07.2017 2.08    Supported RX65N-2MB and RX130-512KB.
*                              Fixed to correspond to Renesas coding rule.
*         : 28.09.2018 2.10    Supported RX66T.
*         : 01.02.2019 2.20    Supported RX72T, RX65N-64pin.
*******************************************************************************/
#ifndef DTC_RX_CONFIG_H
#define DTC_RX_CONFIG_H

#define DTC_DISABLE        (0)
#define DTC_ENABLE         (1)
/*
 * SPECIFY WHETHER TO INCLUDE CODE FOR API PARAMETER CHECKING
 *  0 : Compiles out parameter checking.
 *  1 : Includes parameter checking.
 * Default value is set to BSP_CFG_PARAM_CHECKING_ENABLE to 
 * re-use the system default setting.
*/
#define DTC_CFG_PARAM_CHECKING_ENABLE       (BSP_CFG_PARAM_CHECKING_ENABLE)

/*
 * SPECIFY WHETHER THE DTCER REGISTERS WILL BE CLEARED IN R_DTC_OPEN()
 * DTC_DISABLE : Do nothing.
 * DTC_ENABLE  : Clear all DTCER registers in R_DTC_Open().
*/
#define DTC_CFG_DISABLE_ALL_ACT_SOURCE      (DTC_ENABLE)

/*
 * SPECIFY WHICH ADDRESS MODE IS SUPPORTED BY DTC
 * DTC_DISABLE : Select the Full address mode.
 * DTC_ENABLE  : Select the Short address mode.
*/
#define DTC_CFG_SHORT_ADDRESS_MODE          (DTC_DISABLE)

/*
 * SPECIFY WHETHER THE TRANSFER DATA READ SKIP IS ENABLED
 * DTC_DISABLE : Disable Transfer Data Read Skip.
 * DTC_ENABLE  : Enable Transfer Data Read Skip. 
*/
#define DTC_CFG_TRANSFER_DATA_READ_SKIP_EN  (DTC_ENABLE)

/*
 * SPECIFY WHETHER THE DMAC FIT MODULE IS USED WITH DTC FIT MODULE
 * DTC_DISABLE : DMAC FIT module is not used with DTC FIT module.
 * DTC_ENABLE  : DMAC FIT module is used with DTC FIT module.
*/
#define DTC_CFG_USE_DMAC_FIT_MODULE         (DTC_ENABLE)

/* 
 * SPECIFY WHETHER THE SEQUENCE TRANSFER IS USED
 * Also, set DTC_DISABLE to DTC_CFG_SHORT_ADDRESS_MODE.
 * DTC_DISABLE : Not use sequence transfer.
 * DTC_ENABLE  : Use sequence transfer.
*/
#define DTC_CFG_USE_SEQUENCE_TRANSFER       (DTC_DISABLE)


#endif /* DTC_RX_CONFIG_H */
