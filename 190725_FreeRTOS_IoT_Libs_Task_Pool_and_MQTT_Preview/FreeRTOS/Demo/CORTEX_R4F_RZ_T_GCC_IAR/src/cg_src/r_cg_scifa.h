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
* File Name    : r_cg_scifa.h
* Version      : Code Generator for RZ/T1 V1.00.00.09 [02 Mar 2015]
* Device(s)    : R7S910018CBG
* Tool-Chain   : GCCARM
* Description  : This file implements device driver for SCIF module.
* Creation Date: 19/04/2015
***********************************************************************************************************************/
#ifndef SCIF_H
#define SCIF_H

/***********************************************************************************************************************
Macro definitions (Register bit)
***********************************************************************************************************************/

/*
    Serial mode register (SMR)
*/
/* Clock select (CKS[1:0]) */
#define _SCIF_CLOCK_SERICLK                     (0x0000U) /* SERICLK */
#define _SCIF_CLOCK_SERICLK_4                   (0x0001U) /* SERICLK/4 */
#define _SCIF_CLOCK_SERICLK_16                  (0x0002U) /* SERICLK/16 */
#define _SCIF_CLOCK_SERICLK_64                  (0x0003U) /* SERICLK/64 */
/* Stop bit length (STOP) */
#define _SCIF_STOP_1                            (0x0000U) /* 1 stop bit */
#define _SCIF_STOP_2                            (0x0008U) /* 2 stop bits */
/* Parity mode (PM) */
#define _SCIF_PARITY_EVEN                       (0x0000U) /* Parity even */
#define _SCIF_PARITY_ODD                        (0x0010U) /* Parity odd */
/* Parity enable (PE) */
#define _SCIF_PARITY_DISABLE                    (0x0000U) /* Parity disable */
#define _SCIF_PARITY_ENABLE                     (0x0020U) /* Parity enable */
/* Character length (CHR) */
#define _SCIF_DATA_LENGTH_8                     (0x0000U) /* Data length 8 bits */
#define _SCIF_DATA_LENGTH_7                     (0x0040U) /* Data length 7 bits */
/* Communications mode (CM) */
#define _SCIF_ASYNCHRONOUS_MODE                 (0x0000U) /* Asynchronous mode */
#define _SCIF_CLOCK_SYNCHRONOUS_MODE            (0x0080U) /* Clock synchronous mode */

/*
    Serial control register (SCR)
*/
/* Clock enable (CKE) */
#define _SCIF_INTERNAL_SCK_UNUSED               (0x0000U) /* Internal clock selected, SCK pin unused */
#define _SCIF_INTERNAL_SCK_OUTPUT               (0x0001U) /* Internal clock selected, SCK pin as clock output */
/* Clock enable (CKE) for clock synchronous mode */
#define _SCIF_INTERNAL_SCK_OUTPUT_SYNC          (0x0000U) /* Internal clock, SCK pin is used for clock output */
#define _SCIF_EXTERNAL_SCK_INPUT_SYNC           (0x0002U) /* External clock, SCK pin is used for clock input */
/* Transmit end interrupt enable (TEIE) */
#define _SCIF_TEI_INTERRUPT_DISABLE             (0x0000U) /* TEI interrupt request disable */
#define _SCIF_TEI_INTERRUPT_ENABLE              (0x0004U) /* TEI interrupt request enable */
/* Receive error interrupt enable (REIE) */
#define _SCIF_ERI_BRI_INTERRUPT_DISABLE         (0x0000U) /* Disable receive-error interrupt and break interrupt */
#define _SCIF_ERI_BRI_INTERRUPT_ENABLE          (0x0008U) /* Enable receive-error interrupt and break interrupt */
/* Receive enable (RE) */
#define _SCIF_RECEIVE_DISABLE                   (0x0000U) /* Disable receive mode */
#define _SCIF_RECEIVE_ENABLE                    (0x0010U) /* Enable receive mode */
/* Transmit enable (TE) */
#define _SCIF_TRANSMIT_DISABLE                  (0x0000U) /* Disable transmit mode */
#define _SCIF_TRANSMIT_ENABLE                   (0x0020U) /* Enable transmit mode */
/* Receive interrupt enable (RIE) */
#define _SCIF_RXI_ERI_DISABLE                   (0x0000U) /* Disable RXI and ERI interrupt requests */
#define _SCIF_RXI_ERI_ENABLE                    (0x0040U) /* Enable RXI and ERI interrupt requests */
/* Transmit interrupt enable (TIE) */
#define _SCIF_TXI_DISABLE                       (0x0000U) /* Disable TXI interrupt requests */
#define _SCIF_TXI_ENABLE                        (0x0080U) /* Enable TXI interrupt requests */

/*
    FIFO control register (FCR)
*/
/* Loop-Back test (LOOP) */
#define _SCIF_LOOPBACK_DISABLE                  (0x0000U) /* Loop back test is disabled */
#define _SCIF_LOOPBACK_ENABLE                   (0x0001U) /* Loop back test is enabled */
/* Receive FIFO Data Register Reset (RFRST) */
#define _SCIF_RX_FIFO_RESET_DISABLE             (0x0000U) /* FRDR reset operation is disabled */
#define _SCIF_RX_FIFO_RESET_ENABLE              (0x0002U) /* FRDR reset operation is enabled */
/* Transmit FIFO Data Register Reset (TFRST) */
#define _SCIF_TX_FIFO_RESET_DISABLE             (0x0000U) /* FTDR reset operation is disabled */
#define _SCIF_TX_FIFO_RESET_ENABLE              (0x0004U) /* FTDR reset operation is enabled */
/* Modem control enable (MCE) */
#define _SCIF_MODEM_CONTROL_DISABLE             (0x0000U) /* Model signal is disabled */
#define _SCIF_MODEM_CONTROL_ENABLE              (0x0008U) /* Model signal is enabled */
/* Transmit FIFO Data Trigger Number (TTRG[1:0]) */
#define _SCIF_TX_TRIGGER_NUMBER_8               (0x0000U) /* 8 (or 8 when TDFE flag is 1) */
#define _SCIF_TX_TRIGGER_NUMBER_4               (0x0010U) /* 4 (or 12 when TDFE flag is 1) */
#define _SCIF_TX_TRIGGER_NUMBER_2               (0x0020U) /* 2 (or 14 when TDFE flag is 1) */
#define _SCIF_TX_TRIGGER_NUMBER_0               (0x0030U) /* 0 (or 16 when TDFE flag is 1) */
/* Receive FIFO Data Trigger Number (RTRG[1:0]) */
#define _SCIF_RX_TRIGGER_NUMBER_1               (0x0000U) /* 1 */
#define _SCIF_RX_TRIGGER_NUMBER_4               (0x0040U) /* 4 (for asynchronous mode) */
#define _SCIF_RX_TRIGGER_NUMBER_2               (0x0040U) /* 2 (for clock synchronous mode */
#define _SCIF_RX_TRIGGER_NUMBER_8               (0x0080U) /* 8 */
#define _SCIF_RX_TRIGGER_NUMBER_14              (0x00C0U) /* 14 */
/* RTS# Output Active Trigger Number Select (RSTRG[2:0]) */
#define _SCIF_RTS_TRIGGER_NUMBER_15             (0x0000U) /* 15 */
#define _SCIF_RTS_TRIGGER_NUMBER_1              (0x0100U) /* 1 */
#define _SCIF_RTS_TRIGGER_NUMBER_4              (0x0200U) /* 4 */
#define _SCIF_RTS_TRIGGER_NUMBER_6              (0x0300U) /* 6 */
#define _SCIF_RTS_TRIGGER_NUMBER_8              (0x0400U) /* 8 */
#define _SCIF_RTS_TRIGGER_NUMBER_10             (0x0500U) /* 10 */
#define _SCIF_RTS_TRIGGER_NUMBER_12             (0x0600U) /* 12 */
#define _SCIF_RTS_TRIGGER_NUMBER_14             (0x0700U) /* 14 */

/*
    Serial port register (SPTR)
*/
/* Serial Port Break Data (SPB2DT) */
#define _SCIF_SERIAL_BREAK_DATA_LOW             (0x0000U) /* Input/output data is at low */
#define _SCIF_SERIAL_BREAK_DATA_HIGH            (0x0001U) /* Input/output data is at high */
/* Serial Port Break input/output (SPB2IO) */
#define _SCIF_SERIAL_BREAK_TXD_NO_OUTPUT        (0x0000U) /* SPB2DT bit value is not output to TXD pin */
#define _SCIF_SERIAL_BREAK_TXD_OUTPUT           (0x0002U) /* SPB2DT bit value is output to TXD pin */
/* SCK Port Data (SCKDT) */
#define _SCIF_SCK_DATA_LOW                      (0x0000U) /* Input/output data is at low */
#define _SCIF_SCK_DATA_HIGH                     (0x0004U) /* Input/output data is at high */
/* SCK Port input/output (SCKIO) */
#define _SCIF_SCK_PORT_NO_OUTPUT                (0x0000U) /* SCKDT bit value is not output to SCK pin */
#define _SCIF_SCK_PORT_OUTPUT                   (0x0008U) /* SCKDT bit value is output to SCK pin */
/* CTS# Port Data Select (CTS2DT) */
#define _SCIF_CTS_DATA_0                        (0x0000U) /* Set b4 to 0. Controls CTS# pin with MCE, CTS2IO bit */
#define _SCIF_CTS_DATA_1                        (0x0010U) /* Set b4 to 1. Controls CTS# pin with MCE, CTS2IO bit */
/* CTS# Port Output Specify (CTS2IO) */
#define _SCIF_CTS_OUTPUT_0                      (0x0000U) /* Set b5 to 0. Controls CTS# pin with MCE, CTS2IO bit */
#define _SCIF_CTS_OUTPUT_1                      (0x0020U) /* Set b5 to 1. Controls CTS# pin with MCE, CTS2IO bit */
/* RTS# Port Data Select (RTS2DT) */
#define _SCIF_RTS_DATA_0                        (0x0000U) /* Set b6 to 0. Controls RTS# pin with MCE, RTS2IO bit */
#define _SCIF_RTS_DATA_1                        (0x0040U) /* Set b6 to 1. Controls RTS# pin with MCE, RTS2IO bit */
/* RTS# Port Output Specify (RTS2IO) */
#define _SCIF_RTS_OUTPUT_0                      (0x0000U) /* Set b7 to 0. Controls RTS# pin with MCE, RTS2IO bit */
#define _SCIF_RTS_OUTPUT_1                      (0x0080U) /* Set b7 to 1. Controls RTS# pin with MCE, RTS2IO bit */

/*
    FIFO Trigger Control Register (FTCR)
*/
/* Transmit FIFO Data Trigger Number (TFTC[4:0]) */
#define _SCIF_TX_FIFO_TRIGGER_NUM_0             (0x0000U) /* 0 (no transmit data trigger) */
#define _SCIF_TX_FIFO_TRIGGER_NUM_1             (0x0001U) /* 1 (transmit data triggers) */
#define _SCIF_TX_FIFO_TRIGGER_NUM_2             (0x0002U) /* 2 (transmit data triggers) */
#define _SCIF_TX_FIFO_TRIGGER_NUM_3             (0x0003U) /* 3 (transmit data triggers) */
#define _SCIF_TX_FIFO_TRIGGER_NUM_4             (0x0004U) /* 4 (transmit data triggers) */
#define _SCIF_TX_FIFO_TRIGGER_NUM_5             (0x0005U) /* 5 (transmit data triggers) */
#define _SCIF_TX_FIFO_TRIGGER_NUM_6             (0x0006U) /* 6 (transmit data triggers) */
#define _SCIF_TX_FIFO_TRIGGER_NUM_7             (0x0007U) /* 7 (transmit data triggers) */
#define _SCIF_TX_FIFO_TRIGGER_NUM_8             (0x0008U) /* 8 (transmit data triggers) */
#define _SCIF_TX_FIFO_TRIGGER_NUM_9             (0x0009U) /* 9 (transmit data triggers) */
#define _SCIF_TX_FIFO_TRIGGER_NUM_10            (0x000AU) /* 10 (transmit data triggers) */
#define _SCIF_TX_FIFO_TRIGGER_NUM_11            (0x000BU) /* 11 (transmit data triggers) */
#define _SCIF_TX_FIFO_TRIGGER_NUM_12            (0x000CU) /* 12 (transmit data triggers) */
#define _SCIF_TX_FIFO_TRIGGER_NUM_13            (0x000DU) /* 13 (transmit data triggers) */
#define _SCIF_TX_FIFO_TRIGGER_NUM_14            (0x000EU) /* 14 (transmit data triggers) */
#define _SCIF_TX_FIFO_TRIGGER_NUM_15            (0x000FU) /* 15 (transmit data triggers) */
/* Transmit Trigger Select (TTRGS) */
#define _SCIF_TX_TRIGGER_TTRG_VALID             (0x0000U) /* TTRG[1:0] bits in FCR are valid */
#define _SCIF_TX_TRIGGER_TFTC_VALID             (0x0080U) /* TFTC[4:0] bits in FTCR are valid */
/* Receive FIFO Data Trigger Number (RFTC[4:0]) */
#define _SCIF_RX_FIFO_TRIGGER_NUM_1             (0x0100U) /* 1 (no receive data trigger) */
#define _SCIF_RX_FIFO_TRIGGER_NUM_2             (0x0200U) /* 2 (receive data triggers) */
#define _SCIF_RX_FIFO_TRIGGER_NUM_3             (0x0300U) /* 3 (receive data triggers) */
#define _SCIF_RX_FIFO_TRIGGER_NUM_4             (0x0400U) /* 4 (receive data triggers) */
#define _SCIF_RX_FIFO_TRIGGER_NUM_5             (0x0500U) /* 5 (receive data triggers) */
#define _SCIF_RX_FIFO_TRIGGER_NUM_6             (0x0600U) /* 6 (receive data triggers) */
#define _SCIF_RX_FIFO_TRIGGER_NUM_7             (0x0700U) /* 7 (receive data triggers) */
#define _SCIF_RX_FIFO_TRIGGER_NUM_8             (0x0800U) /* 8 (receive data triggers) */
#define _SCIF_RX_FIFO_TRIGGER_NUM_9             (0x0900U) /* 9 (receive data triggers) */
#define _SCIF_RX_FIFO_TRIGGER_NUM_10            (0x0A00U) /* 10 (receive data triggers) */
#define _SCIF_RX_FIFO_TRIGGER_NUM_11            (0x0B00U) /* 11 (receive data triggers) */
#define _SCIF_RX_FIFO_TRIGGER_NUM_12            (0x0C00U) /* 12 (receive data triggers) */
#define _SCIF_RX_FIFO_TRIGGER_NUM_13            (0x0D00U) /* 13 (receive data triggers) */
#define _SCIF_RX_FIFO_TRIGGER_NUM_14            (0x0E00U) /* 14 (receive data triggers) */
#define _SCIF_RX_FIFO_TRIGGER_NUM_15            (0x0F00U) /* 15 (receive data triggers) */
#define _SCIF_RX_FIFO_TRIGGER_NUM_16            (0x1000U) /* 16 (receive data triggers) */
/* Transmit Trigger Select (RTRGS) */
#define _SCIF_RX_TRIGGER_RTRG_VALID             (0x0000U) /* RTRG[1:0] bits in FCR are valid */
#define _SCIF_RX_TRIGGER_RFTC_VALID             (0x8000U) /* RFTC[4:0] bits in FTCR are valid */

/*
    Serial extended mode register (SEMR)
*/
/* Asynchronous base clock select (ABCS0) */
#define _SCIF_16_BASE_CLOCK                     (0x00U) /* Selects 16 base clock cycles for 1 bit period */
#define _SCIF_8_BASE_CLOCK                      (0x01U) /* Selects 8 base clock cycles for 1 bit period */
/* Noise Cancellation Enable (NFEN) */
#define _SCIF_NOISE_FILTER_DISABLE              (0x00U) /* Noise cancellation for the RxD pin input is disabled */
#define _SCIF_NOISE_FILTER_ENABLE               (0x04U) /* Noise cancellation for the RxD pin input is enabled */
/* Data Transfer Direction Select (DIR) */
#define _SCIF_DATA_TRANSFER_LSB_FIRST           (0x00U) /* Transmits the data in FTDR by the LSB-first method */
#define _SCIF_DATA_TRANSFER_MSB_FIRST           (0x08U) /* Transmits the data in FTDR by the MSB-first method */
/* Modulation Duty Register Select (MDDRS) */
#define _SCIF_BRR_USED                          (0x00U) /* BRR register can be accessed */
#define _SCIF_MDDR_USED                         (0x10U) /* MDDR register can be accessed. */
/* Bit Rate Modulation Enable (BRME) */
#define _SCIF_BIT_RATE_MODULATION_DISABLE       (0x00U) /* Bit rate modulation function is disabled */
#define _SCIF_BIT_RATE_MODULATION_ENABLE        (0x20U) /* Bit rate modulation function is enabled */
/* Baud Rate Generator Double-Speed Mode Select (BGDM) */
#define _SCIF_BAUDRATE_SINGLE                   (0x00U) /* Baud rate generator outputs normal frequency */
#define _SCIF_BAUDRATE_DOUBLE                   (0x80U) /* Baud rate generator doubles output frequency */

/*
    Interrupt Source Priority Register n (PRLn)
*/
/* Interrupt Priority Level Select (PRL[3:0]) */
#define _SCIF_PRIORITY_LEVEL0                   (0x00000000UL) /* Level 0 (highest) */
#define _SCIF_PRIORITY_LEVEL1                   (0x00000001UL) /* Level 1 */
#define _SCIF_PRIORITY_LEVEL2                   (0x00000002UL) /* Level 2 */
#define _SCIF_PRIORITY_LEVEL3                   (0x00000003UL) /* Level 3 */
#define _SCIF_PRIORITY_LEVEL4                   (0x00000004UL) /* Level 4 */
#define _SCIF_PRIORITY_LEVEL5                   (0x00000005UL) /* Level 5 */
#define _SCIF_PRIORITY_LEVEL6                   (0x00000006UL) /* Level 6 */
#define _SCIF_PRIORITY_LEVEL7                   (0x00000007UL) /* Level 7 */
#define _SCIF_PRIORITY_LEVEL8                   (0x00000008UL) /* Level 8 */
#define _SCIF_PRIORITY_LEVEL9                   (0x00000009UL) /* Level 9 */
#define _SCIF_PRIORITY_LEVEL10                  (0x0000000AUL) /* Level 10 */
#define _SCIF_PRIORITY_LEVEL11                  (0x0000000BUL) /* Level 11 */
#define _SCIF_PRIORITY_LEVEL12                  (0x0000000CUL) /* Level 12 */
#define _SCIF_PRIORITY_LEVEL13                  (0x0000000DUL) /* Level 13 */
#define _SCIF_PRIORITY_LEVEL14                  (0x0000000EUL) /* Level 14 */
#define _SCIF_PRIORITY_LEVEL15                  (0x0000000FUL) /* Level 15 */

/* FIFO buffer maximum size */
#define _SCIF_FIFO_MAX_SIZE                     (0x10U) /* Size of 16-stage FIFO buffer */

/***********************************************************************************************************************
Macro definitions
***********************************************************************************************************************/
#define _SCIF_1BIT_INTERVAL_2                (0x0619U)   /* Wait time for 1-bit interval */
#define _SCIF_RX_TRIG_NUM_2                  (0x01U)   /* Receive FIFO data trigger number */

/***********************************************************************************************************************
Typedef definitions
***********************************************************************************************************************/
typedef enum
{
    OVERRUN_ERROR,
    BREAK_DETECT,
    RECEIVE_ERROR
} scif_error_type_t;

/***********************************************************************************************************************
Global functions
***********************************************************************************************************************/
void R_SCIFA2_Create(void);
void R_SCIFA2_Start(void);
void R_SCIFA2_Stop(void);
MD_STATUS R_SCIFA2_Serial_Send(const uint8_t * tx_buf, uint16_t tx_num);
MD_STATUS R_SCIFA2_Serial_Receive(uint8_t * rx_buf, uint16_t rx_num);
void r_scifa2_callback_transmitend(void);
void r_scifa2_callback_receiveend(void);
void r_scifa2_callback_error(scif_error_type_t error_type);

/* Start user code for function. Do not edit comment generated here */

/* Declared volatile to prevent it being optimised out in Release build mode */
extern volatile uint8_t g_uart_in;

/* End user code. Do not edit comment generated here */
#endif
