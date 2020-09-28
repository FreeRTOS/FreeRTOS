/* Generated configuration header file - do not edit */
/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products. No 
* other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all 
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIES REGARDING
* THIS SOFTWARE, WHETHER EXPRESS, IMPLIED OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, 
* FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT. ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED. TO THE MAXIMUM 
* EXTENT PERMITTED NOT PROHIBITED BY LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES 
* SHALL BE LIABLE FOR ANY DIRECT, INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS 
* SOFTWARE, EVEN IF RENESAS OR ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability of 
* this software. By using this software, you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer 
*
* Copyright (C) 2013-2020 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/
/***********************************************************************************************************************
* File Name     : r_sci_rx_config.h
* Description   : Configures the SCI driver
************************************************************************************************************************
* History : DD.MM.YYYY Version Description
*           25.09.2013 1.00    Initial Release
*           17.04.2014 1.20    Added comments for new RX110 support.
*           02.07.2014 1.30    Fixed bug that caused Group12 rx errors to only be enabled for channel 2.
*           25.11.2014 1.40    Added comments for RX113 support
*           30.09.2015 1.70    Added comments for RX23T support
*           01.10.2016 1.80    Added support for RX65N (comments and TX/RX FIFO THRESHOLD options)
*           19.12.2016 1.90    Added comments for RX24U support
*           07.03.2017 2.00    Added comments for RX130-512KB support
*           28.09.2018 2.10    Added comments for RX66T support
*           01.02.2019 2.20    Added comments for RX72T, RX65N-64pin support
*                              Added support received data match function for RX65N
*           28.06.2019 3.10    Added comments for RX23W support
*           15.08.2019 3.20    Added support received data match function for RX72M (SCI0- SCI11)
*                              Added support FIFO mode for RX72M (SCI7 - SCI11)
*           25.11.2019 3.30    Added support RX13T.
*                              Removed support for Generation 1 devices.
*           30.12.2019 3.40    Added support RX66N, RX72N.
*           31.03.2020 3.50    Added support RX23E-A.
***********************************************************************************************************************/
#ifndef SCI_CONFIG_H
#define SCI_CONFIG_H

#include "platform.h"

/***********************************************************************************************************************
Configuration Options
***********************************************************************************************************************/

/* SPECIFY WHETHER TO INCLUDE CODE FOR API PARAMETER CHECKING */
/* Setting to BSP_CFG_PARAM_CHECKING_ENABLE utilizes the system default setting */
/* Setting to 1 includes parameter checking; 0 compiles out parameter checking */
#define SCI_CFG_PARAM_CHECKING_ENABLE   (BSP_CFG_PARAM_CHECKING_ENABLE)

/* SPECIFY WHETHER TO INCLUDE CODE FOR DIFFERENT SCI MODES */
/* Setting an equate to 1 includes code specific to that mode. */
#define SCI_CFG_ASYNC_INCLUDED  (1)
#define SCI_CFG_SYNC_INCLUDED   (0)
#define SCI_CFG_SSPI_INCLUDED   (0)

/* SPECIFY BYTE VALUE TO TRANSMIT WHILE CLOCKING IN DATA IN SSPI MODES */
#define SCI_CFG_DUMMY_TX_BYTE   (0xFF)

/* SPECIFY CHANNELS TO INCLUDE SOFTWARE SUPPORT FOR 1=included, 0=not */
/*
 * NOTE: If using ASYNC mode, adjust BYTEQ_CFG_MAX_CTRL_BLKS in r_byteq_config.h
 * to provide 2 queues per channel (static mode only).
 * * = port connector RSKRX11x
 * u = channel used by the USB-UART port (G1CUSB0)
 * a = this channel is used only for RX130-512KB
 * n = this channel is not available for RX65N-64pin.
 * s = this channel is not available in simple SPI mode.
 * RX MCU supported channels
 *
 * CH#  110 111 113 130 230 231 23T 24T 24U 64M 71M 65N 66T 72T 23W 72M 13T 72N 66N RX23E-A
 * ---  --- --- --- --- --- --- --- --- --- --- --- --- --- --- --- --- --- --- --- -------
 * CH0           X   Xa  X   X               X   X   Xn              X       X   X      
 * CH1   X   X*  X*  Xu  X   X   Xu  Xu  Xu  X   X   Xs  X   X   X   X   X   X   X     Xu
 * CH2           X                           X   X   Xu              X       X   X      
 * CH3                                       X   X   Xs              X       X   X      
 * CH4                                       X   X   Xn              X       X   X      
 * CH5   X   X   X   X   X   Xu  X   X   X   X   X   X   X   X   X   X   X   X   X     X
 * CH6           X   X   X   X       X   X   X   X   Xn  X   X       Xu      X   X     X
 * CH7                                       Xu  Xu  Xn              X       X   X      
 * CH8           X   Xa  X   X           X           X   X   X   Xu  X       X   X      
 * CH9           X   Xa  X   X           X           Xs  X   X       X       X   X      
 * CH10                                              X               X       X   X      
 * CH11                                  X           Xs  X   X       X       X   X      
 * CH12  X   X   X   X   X   X               X   X   Xs  X   X   X   X   X   X   X     X
*/
                                   
#define SCI_CFG_CH0_INCLUDED    (0)
#define SCI_CFG_CH1_INCLUDED    (0)
#define SCI_CFG_CH2_INCLUDED    (1)
#define SCI_CFG_CH3_INCLUDED    (0)
#define SCI_CFG_CH4_INCLUDED    (0)
#define SCI_CFG_CH5_INCLUDED    (0)
#define SCI_CFG_CH6_INCLUDED    (0)
#define SCI_CFG_CH7_INCLUDED    (0)
#define SCI_CFG_CH8_INCLUDED    (0)
#define SCI_CFG_CH9_INCLUDED    (1)
#define SCI_CFG_CH10_INCLUDED   (0)
#define SCI_CFG_CH11_INCLUDED   (0)
#define SCI_CFG_CH12_INCLUDED   (0)

/* SPECIFY ASYNC MODE TX QUEUE BUFFER SIZES (will not allocate if chan not enabled */
#define SCI_CFG_CH0_TX_BUFSIZ   (80)
#define SCI_CFG_CH1_TX_BUFSIZ   (80)
#define SCI_CFG_CH2_TX_BUFSIZ   (80)
#define SCI_CFG_CH3_TX_BUFSIZ   (80)
#define SCI_CFG_CH4_TX_BUFSIZ   (80)
#define SCI_CFG_CH5_TX_BUFSIZ   (80)
#define SCI_CFG_CH6_TX_BUFSIZ   (80)
#define SCI_CFG_CH7_TX_BUFSIZ   (80)
#define SCI_CFG_CH8_TX_BUFSIZ   (80)
#define SCI_CFG_CH9_TX_BUFSIZ   (80)
#define SCI_CFG_CH10_TX_BUFSIZ  (80)
#define SCI_CFG_CH11_TX_BUFSIZ  (80)
#define SCI_CFG_CH12_TX_BUFSIZ  (80)

/* SPECIFY ASYNC MODE RX QUEUE BUFFER SIZES (will not allocate if chan not enabled */
#define SCI_CFG_CH0_RX_BUFSIZ   (80)
#define SCI_CFG_CH1_RX_BUFSIZ   (80)
#define SCI_CFG_CH2_RX_BUFSIZ   (80)
#define SCI_CFG_CH3_RX_BUFSIZ   (80)
#define SCI_CFG_CH4_RX_BUFSIZ   (80)
#define SCI_CFG_CH5_RX_BUFSIZ   (80)
#define SCI_CFG_CH6_RX_BUFSIZ   (80)
#define SCI_CFG_CH7_RX_BUFSIZ   (80)
#define SCI_CFG_CH8_RX_BUFSIZ   (80)
#define SCI_CFG_CH9_RX_BUFSIZ   (80)
#define SCI_CFG_CH10_RX_BUFSIZ  (80)
#define SCI_CFG_CH11_RX_BUFSIZ  (80)
#define SCI_CFG_CH12_RX_BUFSIZ  (80)

/* 
* ENABLE TRANSMIT END INTERRUPT (ASYNCHRONOUS)
* This interrupt only occurs when the last bit of the last byte of data 
* has been sent and the transmitter has become idle. The interrupt calls
* the user's callback function specified in R_SCI_Open() and passes it an
* SCI_EVT_TEI event. A typical use of this feature is to disable an external
* transceiver to save power. It would then be up to the user's code to 
* re-enable the transceiver before sending again. Not including this feature
* reduces code space used by the interrupt. Note that this equate is only
* for including the TEI code. The interrupt itself must be enabled using an
* R_SCI_Control(hdl, SCI_CMD_EN_TEI, NULL) call.
*/
#define SCI_CFG_TEI_INCLUDED    (1)      /* 1=included, 0=not */

/* 
* SET GROUPBL0 (ERI, TEI) INTERRUPT PRIORITY; RX64M/RX71M/RX65N/RX72M/RX72N/RX66N ONLY
* SET GROUPBL1; RX65N ONLY
* SET GROUPAL0 (ERI,TEI) INTERRUPT PRIORITY; RX65N, RX72M, RX72N, RX66N ONLY
* This sets the priority level for receiver overrun, framing, and parity errors
* as well as TEI interrupts for all SCI channels.
*/
#define SCI_CFG_ERI_TEI_PRIORITY (3)     /* (RX64M/RX71M/RX65N/RX72M/RX72N/RX66N ONLY) 1 lowest, 15 highest */

/* ENABLE TX/RX FIFO; (SCIi supported MCU ONLY) 1=included, 0=not */
#define SCI_CFG_CH7_FIFO_INCLUDED   (0)
#define SCI_CFG_CH8_FIFO_INCLUDED   (0)
#define SCI_CFG_CH9_FIFO_INCLUDED   (0)
#define SCI_CFG_CH10_FIFO_INCLUDED  (0)
#define SCI_CFG_CH11_FIFO_INCLUDED  (0)

/* SET TX FIFO THRESHOLD; (SCIi supported MCU ONLY) 0 lowest, 15 highest */
/* TX FIFO THRESHOLD is invalid in Clock Synchronous Mode and Simple SPI Mode. */
/* Set the same value for TX FIFO THRESHOLD and RX FIFO THRESHOLD in Clock Synchronous Mode and Simple SPI Mode. */
#define SCI_CFG_CH7_TX_FIFO_THRESH (8)
#define SCI_CFG_CH8_TX_FIFO_THRESH (8)
#define SCI_CFG_CH9_TX_FIFO_THRESH (8)
#define SCI_CFG_CH10_TX_FIFO_THRESH (8)
#define SCI_CFG_CH11_TX_FIFO_THRESH (8)

/* SET RX FIFO THRESHOLD; (SCIi supported MCU ONLY) 1 lowest, 15 highest */
#define SCI_CFG_CH7_RX_FIFO_THRESH (8)
#define SCI_CFG_CH8_RX_FIFO_THRESH (8)
#define SCI_CFG_CH9_RX_FIFO_THRESH (8)
#define SCI_CFG_CH10_RX_FIFO_THRESH (8)
#define SCI_CFG_CH11_RX_FIFO_THRESH (8)

/* ENABLE Received Data match function (SCIj and SCIi supported MCU RX65N/RX66T/RX72T/RX72M/RX72N/RX66N ONLY) 1=included, 0=not */
#define SCI_CFG_CH0_DATA_MATCH_INCLUDED  (0)
#define SCI_CFG_CH1_DATA_MATCH_INCLUDED  (0)
#define SCI_CFG_CH2_DATA_MATCH_INCLUDED  (0)
#define SCI_CFG_CH3_DATA_MATCH_INCLUDED  (0)
#define SCI_CFG_CH4_DATA_MATCH_INCLUDED  (0)
#define SCI_CFG_CH5_DATA_MATCH_INCLUDED  (0)
#define SCI_CFG_CH6_DATA_MATCH_INCLUDED  (0)
#define SCI_CFG_CH7_DATA_MATCH_INCLUDED  (0)
#define SCI_CFG_CH8_DATA_MATCH_INCLUDED  (0)
#define SCI_CFG_CH9_DATA_MATCH_INCLUDED  (0)
#define SCI_CFG_CH10_DATA_MATCH_INCLUDED (0)
#define SCI_CFG_CH11_DATA_MATCH_INCLUDED (0)

#endif /* SCI_CONFIG_H */
