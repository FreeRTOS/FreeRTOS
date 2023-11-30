/*******************************************************************************
 * (c) Copyright 2007-2017 Microsemi SoC Products Group. All rights reserved.
 * 
 * SVN $Revision: 9082 $
 * SVN $Date: 2017-04-28 11:51:36 +0530 (Fri, 28 Apr 2017) $
 */

#ifndef __CORE_UART_APB_REGISTERS
#define __CORE_UART_APB_REGISTERS   1

#ifdef __cplusplus
extern "C" {
#endif

/*------------------------------------------------------------------------------
 * TxData register details
 */
#define TXDATA_REG_OFFSET   0x0u

/*
 * TxData bits.
 */
#define TXDATA_OFFSET   0x0u
#define TXDATA_MASK     0xFFu
#define TXDATA_SHIFT    0u

/*------------------------------------------------------------------------------
 * RxData register details
 */
#define RXDATA_REG_OFFSET   0x4u

/*
 * RxData bits.
 */
#define RXDATA_OFFSET   0x4u
#define RXDATA_MASK     0xFFu
#define RXDATA_SHIFT    0u

/*------------------------------------------------------------------------------
 * ControReg1 register details
 */
#define CTRL1_REG_OFFSET        0x8u

/*
 * Baud value (Lower 8-bits)
 */
#define CTRL1_BAUDVALUE_OFFSET   0x8u
#define CTRL1_BAUDVALUE_MASK     0xFFu
#define CTRL1_BAUDVALUE_SHIFT    0u

/*------------------------------------------------------------------------------
 * ControReg2 register details
 */
#define CTRL2_REG_OFFSET          0xCu

/*
 * Bit length
 */
#define CTRL2_BIT_LENGTH_OFFSET   0xCu
#define CTRL2_BIT_LENGTH_MASK     0x01u
#define CTRL2_BIT_LENGTH_SHIFT    0u

/*
 * Parity enable.
 */
#define CTRL2_PARITY_EN_OFFSET    0xCu
#define CTRL2_PARITY_EN_MASK      0x02u
#define CTRL2_PARITY_EN_SHIFT     1u

/*
 * Odd/even parity selection.
 */
#define CTRL2_ODD_EVEN_OFFSET     0xCu
#define CTRL2_ODD_EVEN_MASK       0x04u
#define CTRL2_ODD_EVEN_SHIFT      2u

/*
 *  Baud value (Higher 5-bits)
 */
#define CTRL2_BAUDVALUE_OFFSET    0xCu
#define CTRL2_BAUDVALUE_MASK      0xF8u
#define CTRL2_BAUDVALUE_SHIFT     3u

/*------------------------------------------------------------------------------
 * StatusReg register details
 */
#define StatusReg_REG_OFFSET    0x10u

#define STATUS_REG_OFFSET       0x10u

/*
 * Transmit ready.
 */
#define STATUS_TXRDY_OFFSET   0x10u
#define STATUS_TXRDY_MASK     0x01u
#define STATUS_TXRDY_SHIFT    0u

/*
 * Receive full.
 */
#define STATUS_RXFULL_OFFSET   0x10u
#define STATUS_RXFULL_MASK     0x02u
#define STATUS_RXFULL_SHIFT    1u

/*
 * Parity error.
 */
#define STATUS_PARITYERR_OFFSET   0x10u
#define STATUS_PARITYERR_MASK     0x04u
#define STATUS_PARITYERR_SHIFT    2u

/*
 * Overflow.
 */
#define STATUS_OVERFLOW_OFFSET   0x10u
#define STATUS_OVERFLOW_MASK     0x08u
#define STATUS_OVERFLOW_SHIFT    3u

/*
 * Frame Error.
 */
#define STATUS_FRAMERR_OFFSET   0x10u
#define STATUS_FRAMERR_MASK     0x10u
#define STATUS_FRAMERR_SHIFT    4u

#ifdef __cplusplus
}
#endif

#endif	/* __CORE_UART_APB_REGISTERS */
