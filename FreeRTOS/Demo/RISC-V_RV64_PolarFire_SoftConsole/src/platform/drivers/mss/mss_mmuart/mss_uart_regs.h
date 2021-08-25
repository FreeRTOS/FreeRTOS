 /*******************************************************************************
 * Copyright 2019-2020 Microchip FPGA Embedded Systems Solutions.
 *
 * SPDX-License-Identifier: MIT
 * 
 * Register bit offsets and masks definitions for PolarFire SoC MSS MMUART
 * 
 */

#ifndef MSS_UART_REGS_H_
#define MSS_UART_REGS_H_

#ifdef __cplusplus
extern "C" {
#endif

/*******************************************************************************
 Register Bit definitions
 */

/* Line Control register bit definitions */
#define SB                          6u                  /* Set break */
#define DLAB                        7u                  /* Divisor latch access bit */

/* Line Control register bit masks */
#define SB_MASK                     (0x01u << SB)        /* Set break */
#define DLAB_MASK                   (0x01u << DLAB)      /* Divisor latch access bit */

/* FIFO Control register bit definitions */
#define RXRDY_TXRDYN_EN             0u                  /* Enable TXRDY and RXRDY signals */
#define CLEAR_RX_FIFO               1u                  /* Clear receiver FIFO */
#define CLEAR_TX_FIFO               2u                  /* Clear transmitter FIFO */
#define RDYMODE                     3u                  /* Mode 0 or Mode 1 for TXRDY and RXRDY */

/* FIFO Control register bit MASKS */
#define RXRDY_TXRDYN_EN_MASK        (0x01u << 0u)      /* Enable TXRDY and RXRDY signals */
#define CLEAR_RX_FIFO_MASK          (0x01u << 1u)      /* Clear receiver FIFO */
#define CLEAR_TX_FIFO_MASK          (0x01u << 2u)      /* Clear transmitter FIFO */
#define RDYMODE_MASK                (0x01u << 3u)      /* Mode 0 or Mode 1 for TXRDY and RXRDY */

/* Modem Control register bit definitions */
#define LOOP                        4u                  /* Local loopback */
#define RLOOP                       5u                  /* Remote loopback */
#define ECHO                        6u                  /* Automatic echo */

/* Modem Control register bit MASKS */
#define LOOP_MASK                   (0x01u << 4u)        /* Local loopback */
#define RLOOP_MASK                  (0x01u << 5u)        /* Remote loopback & Automatic echo*/
#define ECHO_MASK                   (0x01u << 6u)        /* Automatic echo */

/* Line Status register bit definitions   */
#define DR                          0u                  /* Data ready */
#define THRE                        5u                  /* Transmitter holding register empty */
#define TEMT                        6u                  /* Transmitter empty */

/* Line Status register bit MASKS   */
#define DR_MASK                     (0x01u << 0u)        /* Data ready */
#define THRE_MASK                   (0x01u << 5u)        /* Transmitter holding register empty */
#define TEMT_MASK                   (0x01u << 6u)        /* Transmitter empty */

/* Interrupt Enable register bit definitions */
#define ERBFI                       0u                  /* Enable receiver buffer full interrupt */
#define ETBEI                       1u                  /* Enable transmitter buffer empty interrupt */
#define ELSI                        2u                  /* Enable line status interrupt */
#define EDSSI                       3u                  /* Enable modem status interrupt */

/* Interrupt Enable register bit MASKS */
#define ERBFI_MASK                  (0x01u << 0u)      /* Enable receiver buffer full interrupt */
#define ETBEI_MASK                  (0x01u << 1u)      /* Enable transmitter buffer empty interrupt */
#define ELSI_MASK                   (0x01u << 2u)      /* Enable line status interrupt */
#define EDSSI_MASK                  (0x01u << 3u)      /* Enable modem status interrupt */

/* Multimode register 0 bit definitions */
#define ELIN                        3u                  /* Enable LIN header detection */
#define ETTG                        5u                  /* Enable transmitter time guard */
#define ERTO                        6u                  /* Enable receiver time-out */
#define EFBR                        7u                  /* Enable fractional baud rate mode */

/* Multimode register 0 bit MASKS */
#define ELIN_MASK                   (0x01u << 3u)      /* Enable LIN header detection */
#define ETTG_MASK                   (0x01u << 5u)      /* Enable transmitter time guard */
#define ERTO_MASK                   (0x01u << 6u)      /* Enable receiver time-out */
#define EFBR_MASK                   (0x01u << 7u)      /* Enable fractional baud rate mode */

/* Multimode register 1 bit definitions */
#define E_MSB_RX                    0u                  /* MSB / LSB first for receiver */
#define E_MSB_TX                    1u                  /* MSB / LSB first for transmitter */
#define EIRD                        2u                  /* Enable IrDA modem */
#define EIRX                        3u                  /* Input polarity for IrDA modem */
#define EITX                        4u                  /* Output polarity for IrDA modem */
#define EITP                        5u                  /* Output pulse width for IrDA modem */

/* Multimode register 1 bit MASKS */
#define E_MSB_RX_MASK               (0x01u << 0u)      /* MSB / LSB first for receiver */
#define E_MSB_TX_MASK               (0x01u << 1u)      /* MSB / LSB first for transmitter */
#define EIRD_MASK                   (0x01u << 2u)      /* Enable IrDA modem */
#define EIRX_MASK                   (0x01u << 3u)      /* Input polarity for IrDA modem */
#define EITX_MASK                   (0x01u << 4u)      /* Output polarity for IrDA modem */
#define EITP_MASK                   (0x01u << 5u)      /* Output pulse width for IrDA modem */

/* Multimode register 2 bit definitions */
#define EERR                        0u                  /* Enable ERR / NACK during stop time */
#define EAFM                        1u                  /* Enable 9-bit address flag mode */
#define EAFC                        2u                  /* Enable address flag clear */
#define ESWM                        3u                  /* Enable single wire half-duplex mode */

/* Multimode register 2 bit MASKS */
#define EERR_MASK                   (0x01u << 0u)      /* Enable ERR / NACK during stop time */
#define EAFM_MASK                   (0x01u << 1u)      /* Enable 9-bit address flag mode */
#define EAFC_MASK                   (0x01u << 2u)      /* Enable address flag clear */
#define ESWM_MASK                   (0x01u << 3u)      /* Enable single wire half-duplex mode */

/* Multimode Interrupt Enable register and
   Multimode Interrupt Identification register definitions */
#define ERTOI                       0u                  /* Enable receiver timeout interrupt */
#define ENACKI                      1u                  /* Enable NACK / ERR interrupt */
#define EPID_PEI                    2u                  /* Enable PID parity error interrupt */
#define ELINBI                      3u                  /* Enable LIN break interrupt */
#define ELINSI                      4u                  /* Enable LIN sync detection interrupt */

/* Multimode Interrupt Enable register and
   Multimode Interrupt Identification register MASKS */
#define ERTOI_MASK                  (0x01u << 0u)      /* Enable receiver timeout interrupt */
#define ENACKI_MASK                 (0x01u << 1u)      /* Enable NACK / ERR interrupt */
#define EPID_PEI_MASK               (0x01u << 2u)      /* Enable PID parity error interrupt */
#define ELINBI_MASK                 (0x01u << 3u)      /* Enable LIN break interrupt */
#define ELINSI_MASK                 (0x01u << 4u)      /* Enable LIN sync detection interrupt */

#ifdef __cplusplus                       
}
#endif

#endif /* MSS_UART_REGS_H_ */
