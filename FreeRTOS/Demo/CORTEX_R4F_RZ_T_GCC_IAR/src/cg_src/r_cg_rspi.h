/***********************************************************************************************************************
* DISCLAIMER
* This software is supplied by Renesas Electronics Corporation and is only intended for use with Renesas products.
* No other uses are authorized. This software is owned by Renesas Electronics Corporation and is protected under all
* applicable laws, including copyright laws. 
* THIS SOFTWARE IS PROVIDED "AS IS" AND RENESAS MAKES NO WARRANTIESREGARDING THIS SOFTWARE, WHETHER EXPRESS, IMPLIED
* OR STATUTORY, INCLUDING BUT NOT LIMITED TO WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
* NON-INFRINGEMENT.  ALL SUCH WARRANTIES ARE EXPRESSLY DISCLAIMED.TO THE MAXIMUM EXTENT PERMITTED NOT PROHIBITED BY
* LAW, NEITHER RENESAS ELECTRONICS CORPORATION NOR ANY OF ITS AFFILIATED COMPANIES SHALL BE LIABLE FOR ANY DIRECT,
* INDIRECT, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES FOR ANY REASON RELATED TO THIS SOFTWARE, EVEN IF RENESAS OR
* ITS AFFILIATES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGES.
* Renesas reserves the right, without notice, to make changes to this software and to discontinue the availability 
* of this software. By using this software, you agree to the additional terms and conditions found by accessing the 
* following link:
* http://www.renesas.com/disclaimer
*
* Copyright (C) 2015 Renesas Electronics Corporation. All rights reserved.
***********************************************************************************************************************/

/***********************************************************************************************************************
* File Name    : r_cg_rspi.h
* Version      : Code Generator for RZ/T1 V1.00.00.09 [02 Mar 2015]
* Device(s)    : R7S910018CBG
* Tool-Chain   : GCCARM
* Description  : This file implements device driver for RSPI module.
* Creation Date: 22/04/2015
***********************************************************************************************************************/
#ifndef RSPI_H
#define RSPI_H

/***********************************************************************************************************************
Macro definitions (Register bit)
***********************************************************************************************************************/
/*
    RSPI Control Register (SPCR)
*/
/* RSPI Mode Select (SPMS) */
#define _RSPI_MODE_SPI                       (0x00U) /* SPI operation (four-wire method) */
#define _RSPI_MODE_CLOCK_SYNCHRONOUS         (0x01U) /* Clock synchronous operation (three-wire method) */
/* Communications Operating Mode Select (TXMD) */
#define _RSPI_FULL_DUPLEX_SYNCHRONOUS        (0x00U) /* Full-duplex synchronous serial communications */
#define _RSPI_TRANSMIT_ONLY                  (0x02U) /* Serial communications with transmit only operations */
/* Mode Fault Error Detection Enable (MODFEN) */
#define _RSPI_MODE_FAULT_DETECT_DISABLED     (0x00U) /* Disables the detection of mode fault error */
#define _RSPI_MODE_FAULT_DETECT_ENABLED      (0x04U) /* Enables the detection of mode fault error */
/* RSPI Master/Slave Mode Select (MSTR) */
#define _RSPI_SLAVE_MODE                     (0x00U) /* Slave mode */
#define _RSPI_MASTER_MODE                    (0x08U) /* Master mode */
/* RSPI Error Interrupt Enable (SPEIE) */
#define _RSPI_ERROR_INTERRUPT_DISABLED       (0x00U) /* Disables the generation of RSPI error interrupt */
#define _RSPI_ERROR_INTERRUPT_ENABLED        (0x10U) /* Enables the generation of RSPI error interrupt */
/* RSPI Transmit Interrupt Enable (SPTIE) */
#define _RSPI_TRANSMIT_INTERRUPT_DISABLED    (0x00U) /* Disables the generation of RSPI transmit interrupt */
#define _RSPI_TRANSMIT_INTERRUPT_ENABLED     (0x20U) /* Enables the generation of RSPI transmit interrupt */
/* RSPI Function Enable (SPE) */
#define _RSPI_FUNCTION_DISABLED              (0x00U) /* Disables the RSPI function */
#define _RSPI_FUNCTION_ENABLED               (0x40U) /* Enables the RSPI function */
/* RSPI Receive Interrupt Enable (SPRIE) */
#define _RSPI_RECEIVE_INTERRUPT_DISABLED     (0x00U) /* Disables the generation of RSPI receive interrupt */
#define _RSPI_RECEIVE_INTERRUPT_ENABLED      (0x80U) /* Enables the generation of RSPI receive interrupt */

/*
    RSPI Slave Select Polarity Register (SSLP)
*/
/* SSL0 Signal Polarity Setting (SSL0P) */
#define _RSPI_SSL0_POLARITY_LOW              (0x00U) /* SSL0 signal is active low */
#define _RSPI_SSL0_POLARITY_HIGH             (0x01U) /* SSL0 signal is active high */
/* SSL1 Signal Polarity Setting (SSL1P) */
#define _RSPI_SSL1_POLARITY_LOW              (0x00U) /* SSL1 signal is active low */
#define _RSPI_SSL1_POLARITY_HIGH             (0x02U) /* SSL1 signal is active high */
/* SSL2 Signal Polarity Setting (SSL2P) */
#define _RSPI_SSL2_POLARITY_LOW              (0x00U) /* SSL2 signal is active low */
#define _RSPI_SSL2_POLARITY_HIGH             (0x04U) /* SSL2 signal is active high */
/* SSL3 Signal Polarity Setting (SSL3P) */
#define _RSPI_SSL3_POLARITY_LOW              (0x00U) /* SSL3 signal is active low */
#define _RSPI_SSL3_POLARITY_HIGH             (0x08U) /* SSL3 signal is active high */

/*
    RSPI Pin Control Register (SPPCR)
*/
/* RSPI Loopback (SPLP) */
#define _RSPI_LOOPBACK_DISABLED              (0x00U) /* Normal mode */
#define _RSPI_LOOPBACK_ENABLED               (0x01U) /* Loopback mode (reversed transmit data = receive data) */
/* RSPI Loopback 2 (SPLP2) */
#define _RSPI_LOOPBACK2_DISABLED             (0x00U) /* Normal mode */
#define _RSPI_LOOPBACK2_ENABLED              (0x02U) /* Loopback mode (transmit data = receive data) */
/* Output pin mode (SPOM) */
#define _RSPI_OUTPUT_PIN_CMOS                (0x00U) /* CMOS output */
#define _RSPI_OUTPUT_PIN_OPEN_DRAIN          (0x04U) /* Open-drain output */
/* MOSI Idle Fixed Value (MOIFV) */
#define _RSPI_MOSI_LEVEL_LOW                 (0x00U) /* Level output on MOSIA during idling corresponds to low */
#define _RSPI_MOSI_LEVEL_HIGH                (0x10U) /* Level output on MOSIA during idling corresponds to high */
/* MOSI Idle Value Fixing Enable (MOIFE) */
#define _RSPI_MOSI_FIXING_PREV_TRANSFER      (0x00U) /* MOSI output value equals final data from previous transfer */
#define _RSPI_MOSI_FIXING_MOIFV_BIT          (0x20U) /* MOSI output value equals the value set in the MOIFV bit */

/*
    RSPI Sequence Control Register (SPSCR)
*/
/* RSPI Sequence Length Specification (SPSLN[2:0]) */
#define _RSPI_SEQUENCE_LENGTH_1              (0x00U) /* 0 -> 0... */
#define _RSPI_SEQUENCE_LENGTH_2              (0x01U) /* 0 -> 1 -> 0... */
#define _RSPI_SEQUENCE_LENGTH_3              (0x02U) /* 0 -> 1 -> 2 -> 0... */
#define _RSPI_SEQUENCE_LENGTH_4              (0x03U) /* 0 -> 1 -> 2 -> 3 -> 0... */
#define _RSPI_SEQUENCE_LENGTH_5              (0x04U) /* 0 -> 1 -> 2 -> 3 -> 4 -> 0... */
#define _RSPI_SEQUENCE_LENGTH_6              (0x05U) /* 0 -> 1 -> 2 -> 3 -> 4 -> 5 -> 0... */
#define _RSPI_SEQUENCE_LENGTH_7              (0x06U) /* 0 -> 1 -> 2 -> 3 -> 4 -> 5 -> 6 -> 0... */
#define _RSPI_SEQUENCE_LENGTH_8              (0x07U) /* 0 -> 1 -> 2 -> 3 -> 4 -> 5 -> 6 -> 7 -> 0... */

/*
    RSPI Data Control Register (SPDCR)
*/
/* Number of Frames Specification (SPFC[1:0]) */
#define _RSPI_FRAMES_1                       (0x00U) /* 1 frame */
#define _RSPI_FRAMES_2                       (0x01U) /* 2 frames */
#define _RSPI_FRAMES_3                       (0x02U) /* 3 frames */
#define _RSPI_FRAMES_4                       (0x03U) /* 4 frames */
/* RSPI Receive/Transmit Data Selection (SPRDTD) */
#define _RSPI_READ_SPDR_RX_BUFFER            (0x00U) /* read SPDR values from receive buffer */
#define _RSPI_READ_SPDR_TX_BUFFER            (0x10U) /* read SPDR values from transmit buffer (transmit buffer empty) */
/* RSPI Longword Access/Word Access Specification (SPLW) */ 
#define _RSPI_ACCESS_WORD                    (0x00U) /* SPDR is accessed in words */
#define _RSPI_ACCESS_LONGWORD                (0x20U) /* SPDR is accessed in longwords */

/*
    RSPI Clock Delay Register (SPCKD)
*/
/* RSPCK Delay Setting (SCKDL[2:0]) */
#define _RSPI_RSPCK_DELAY_1                  (0x00U) /* 1 RSPCK */
#define _RSPI_RSPCK_DELAY_2                  (0x01U) /* 2 RSPCK */
#define _RSPI_RSPCK_DELAY_3                  (0x02U) /* 3 RSPCK */
#define _RSPI_RSPCK_DELAY_4                  (0x03U) /* 4 RSPCK */
#define _RSPI_RSPCK_DELAY_5                  (0x04U) /* 5 RSPCK */
#define _RSPI_RSPCK_DELAY_6                  (0x05U) /* 6 RSPCK */
#define _RSPI_RSPCK_DELAY_7                  (0x06U) /* 7 RSPCK */
#define _RSPI_RSPCK_DELAY_8                  (0x07U) /* 8 RSPCK */

/*
    RSPI Slave Select Negation Delay Register (SSLND)
*/
/* SSL Negation Delay Setting (SLNDL[2:0]) */
#define _RSPI_SSL_NEGATION_DELAY_1           (0x00U) /* 1 RSPCK */
#define _RSPI_SSL_NEGATION_DELAY_2           (0x01U) /* 2 RSPCK */
#define _RSPI_SSL_NEGATION_DELAY_3           (0x02U) /* 3 RSPCK */
#define _RSPI_SSL_NEGATION_DELAY_4           (0x03U) /* 4 RSPCK */
#define _RSPI_SSL_NEGATION_DELAY_5           (0x04U) /* 5 RSPCK */
#define _RSPI_SSL_NEGATION_DELAY_6           (0x05U) /* 6 RSPCK */
#define _RSPI_SSL_NEGATION_DELAY_7           (0x06U) /* 7 RSPCK */
#define _RSPI_SSL_NEGATION_DELAY_8           (0x07U) /* 8 RSPCK */

/*
    RSPI Next-Access Delay Register (SPND)
*/
/* RSPI Next-Access Delay Setting (SPNDL[2:0]) */
#define _RSPI_NEXT_ACCESS_DELAY_1            (0x00U) /* 1 RSPCK + 2 SERICLK */
#define _RSPI_NEXT_ACCESS_DELAY_2            (0x01U) /* 2 RSPCK + 2 SERICLK */
#define _RSPI_NEXT_ACCESS_DELAY_3            (0x02U) /* 3 RSPCK + 2 SERICLK */
#define _RSPI_NEXT_ACCESS_DELAY_4            (0x03U) /* 4 RSPCK + 2 SERICLK */
#define _RSPI_NEXT_ACCESS_DELAY_5            (0x04U) /* 5 RSPCK + 2 SERICLK */
#define _RSPI_NEXT_ACCESS_DELAY_6            (0x05U) /* 6 RSPCK + 2 SERICLK */
#define _RSPI_NEXT_ACCESS_DELAY_7            (0x06U) /* 7 RSPCK + 2 SERICLK */
#define _RSPI_NEXT_ACCESS_DELAY_8            (0x07U) /* 8 RSPCK + 2 SERICLK */

/*
    RSPI Control Register 2 (SPCR2)
*/
/* Parity Enable (SPPE) */
#define _RSPI_PARITY_DISABLE                 (0x00U) /* Does not add parity bit to transmit data */
#define _RSPI_PARITY_ENABLE                  (0x01U) /* Adds the parity bit to transmit data */
/* Parity Mode (SPOE) */
#define _RSPI_PARITY_EVEN                    (0x00U) /* Selects even parity for use in transmission and reception */
#define _RSPI_PARITY_ODD                     (0x02U) /* Selects odd parity for use in transmission and reception */
/* RSPI Idle Interrupt Enable (SPIIE) */
#define _RSPI_IDLE_INTERRUPT_DISABLED        (0x00U) /* Disables the generation of RSPI idle interrupt */
#define _RSPI_IDLE_INTERRUPT_ENABLED         (0x04U) /* Enables the generation of RSPI idle interrupt */
/* Parity Self-Testing (PTE) */
#define _RSPI_SELF_TEST_DISABLED             (0x00U) /* Disables the self-diagnosis function of the parity circuit */
#define _RSPI_SELF_TEST_ENABLED              (0x08U) /* Enables the self-diagnosis function of the parity circuit */
/* RSPCK Auto-Stop Function Enable (SCKASE) */
#define _RSPI_AUTO_STOP_DISABLED             (0x00U) /* Disables the RSPCK auto-stop function */
#define _RSPI_AUTO_STOP_ENABLED              (0x10U) /* Enables the RSPCK auto-stop function */

/*
    RSPI Command Registers 0 to 7 (SPCMD0 to SPCMD7)
*/
/* RSPCK Phase Setting (CPHA) */
#define _RSPI_RSPCK_SAMPLING_ODD           (0x0000U) /* Data sampling on odd edge, data variation on even edge */
#define _RSPI_RSPCK_SAMPLING_EVEN          (0x0001U) /* Data variation on odd edge, data sampling on even edge */
/* RSPCK Polarity Setting (CPOL) */
#define _RSPI_RSPCK_POLARITY_LOW           (0x0000U) /* RSPCK is low when idle */
#define _RSPI_RSPCK_POLARITY_HIGH          (0x0002U) /* RSPCK is high when idle */
/* Bit Rate Division Setting (BRDV[1:0]) */
#define _RSPI_BASE_BITRATE_1               (0x0000U) /* These bits select the base bit rate */
#define _RSPI_BASE_BITRATE_2               (0x0004U) /* These bits select the base bit rate divided by 2 */
#define _RSPI_BASE_BITRATE_4               (0x0008U) /* These bits select the base bit rate divided by 4 */
#define _RSPI_BASE_BITRATE_8               (0x000CU) /* These bits select the base bit rate divided by 8 */
/* SSL Signal Assertion Setting (SSLA[2:0]) */
#define _RSPI_SIGNAL_ASSERT_SSL0           (0x0000U) /* SSL0 */
#define _RSPI_SIGNAL_ASSERT_SSL1           (0x0010U) /* SSL1 */
#define _RSPI_SIGNAL_ASSERT_SSL2           (0x0020U) /* SSL2 */
#define _RSPI_SIGNAL_ASSERT_SSL3           (0x0030U) /* SSL3 */
/* SSL Signal Level Keeping (SSLKP) */
#define _RSPI_SSL_KEEP_DISABLE             (0x0000U) /* Negates all SSL signals upon completion of transfer */
#define _RSPI_SSL_KEEP_ENABLE              (0x0080U) /* Keep SSL level from end of transfer till next access */
/* RSPI Data Length Setting (SPB[3:0]) */
#define _RSPI_DATA_LENGTH_BITS_8           (0x0400U) /* 8 bits */
#define _RSPI_DATA_LENGTH_BITS_9           (0x0800U) /* 9 bits */
#define _RSPI_DATA_LENGTH_BITS_10          (0x0900U) /* 10 bits */
#define _RSPI_DATA_LENGTH_BITS_11          (0x0A00U) /* 11 bits */
#define _RSPI_DATA_LENGTH_BITS_12          (0x0B00U) /* 12 bits */
#define _RSPI_DATA_LENGTH_BITS_13          (0x0C00U) /* 13 bits */
#define _RSPI_DATA_LENGTH_BITS_14          (0x0D00U) /* 14 bits */
#define _RSPI_DATA_LENGTH_BITS_15          (0x0E00U) /* 15 bits */
#define _RSPI_DATA_LENGTH_BITS_16          (0x0F00U) /* 16 bits */
#define _RSPI_DATA_LENGTH_BITS_20          (0x0000U) /* 20 bits */
#define _RSPI_DATA_LENGTH_BITS_24          (0x0100U) /* 24 bits */
#define _RSPI_DATA_LENGTH_BITS_32          (0x0200U) /* 32 bits */
/* RSPI LSB First (LSBF) */
#define _RSPI_MSB_FIRST                    (0x0000U) /* MSB first */
#define _RSPI_LSB_FIRST                    (0x1000U) /* LSB first */
/* RSPI Next-Access Delay Enable (SPNDEN) */
#define _RSPI_NEXT_ACCESS_DELAY_DISABLE    (0x0000U) /* Next-access delay of 1 RSPCK + 2 SERICLK */
#define _RSPI_NEXT_ACCESS_DELAY_ENABLE     (0x2000U) /* Next-access delay equal to setting of SPND register */
/* SSL Negation Delay Setting Enable (SLNDEN) */
#define _RSPI_NEGATION_DELAY_DISABLE       (0x0000U) /* SSL negation delay of 1 RSPCK */
#define _RSPI_NEGATION_DELAY_ENABLE        (0x4000U) /* SSL negation delay equal to setting of SSLND register */
/* RSPCK Delay Setting Enable (SCKDEN) */
#define _RSPI_RSPCK_DELAY_DISABLE          (0x0000U) /* RSPCK delay of 1 RSPCK */
#define _RSPI_RSPCK_DELAY_ENABLE           (0x8000U) /* RSPCK delay equal to setting of the SPCKD register */

/*
    Interrupt Priority Level Store Register n (PRLn)
*/
/* Interrupt Priority Level Store (PRL[3:0]) */
#define _RSPI_PRIORITY_LEVEL0                (0x00000000UL) /* Level 0 (highest) */
#define _RSPI_PRIORITY_LEVEL1                (0x00000001UL) /* Level 1 */
#define _RSPI_PRIORITY_LEVEL2                (0x00000002UL) /* Level 2 */
#define _RSPI_PRIORITY_LEVEL3                (0x00000003UL) /* Level 3 */
#define _RSPI_PRIORITY_LEVEL4                (0x00000004UL) /* Level 4 */
#define _RSPI_PRIORITY_LEVEL5                (0x00000005UL) /* Level 5 */
#define _RSPI_PRIORITY_LEVEL6                (0x00000006UL) /* Level 6 */
#define _RSPI_PRIORITY_LEVEL7                (0x00000007UL) /* Level 7 */
#define _RSPI_PRIORITY_LEVEL8                (0x00000008UL) /* Level 8 */
#define _RSPI_PRIORITY_LEVEL9                (0x00000009UL) /* Level 9 */
#define _RSPI_PRIORITY_LEVEL10               (0x0000000AUL) /* Level 10 */
#define _RSPI_PRIORITY_LEVEL11               (0x0000000BUL) /* Level 11 */
#define _RSPI_PRIORITY_LEVEL12               (0x0000000CUL) /* Level 12 */
#define _RSPI_PRIORITY_LEVEL13               (0x0000000DUL) /* Level 13 */
#define _RSPI_PRIORITY_LEVEL14               (0x0000000EUL) /* Level 14 */
#define _RSPI_PRIORITY_LEVEL15               (0x0000000FUL) /* Level 15 */


/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
#define _RSPI1_DIVISOR                       (0x4AU)

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/

/***********************************************************************************************************************
Global functions
***********************************************************************************************************************/
void R_RSPI1_Create(void);
void R_RSPI1_Start(void);
void R_RSPI1_Stop(void);
MD_STATUS R_RSPI1_Send(const uint32_t * tx_buf, uint16_t tx_num);
void r_rspi1_callback_transmitend(void);
void r_rspi1_callback_error(uint8_t err_type);

/* Start user code for function. Do not edit comment generated here */
/* End user code. Do not edit comment generated here */
#endif
