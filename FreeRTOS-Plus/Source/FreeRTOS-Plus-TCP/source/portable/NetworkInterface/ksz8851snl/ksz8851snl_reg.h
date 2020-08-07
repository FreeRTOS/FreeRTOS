/**
 *
 * \file
 *
 * \brief KS8851SNL registers definitions.
 *
 * Copyright (c) 2013-2015 Atmel Corporation. All rights reserved.
 *
 * \asf_license_start
 *
 * \page License
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 *    this list of conditions and the following disclaimer in the documentation
 *    and/or other materials provided with the distribution.
 *
 * 3. The name of Atmel may not be used to endorse or promote products derived
 *    from this software without specific prior written permission.
 *
 * 4. This software may only be redistributed and used in connection with an
 *    Atmel microcontroller product.
 *
 * THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR IMPLIED
 * WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * EXPRESSLY AND SPECIFICALLY DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR
 * ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * \asf_license_stop
 *
 */
/*
 * Support and FAQ: visit <a href="http://www.atmel.com/design-support/">Atmel Support</a>
 */

#ifndef KSZ8851SNL_REG_H_INCLUDED
#define KSZ8851SNL_REG_H_INCLUDED

#define REG_ADDR_MASK              (0x3F0)      /* Register address mask */
#define OPCODE_MASK                (3 << 14)
#define CMD_READ                   (0 << 14)
#define CMD_WRITE                  (1 << 14)
#define FIFO_READ                  (0x80)
#define FIFO_WRITE                 (0xC0)

/*
 * MAC Registers
 * (Offset 0x00 - 0x25)
 */
#define REG_BUS_ERROR_STATUS       (0x06)       /* BESR */
#define   BUS_ERROR_IBEC              (0x8000)
#define   BUS_ERROR_IBECV_MASK        (0x7800)    /* Default IPSec clock at 166Mhz */

#define REG_CHIP_CFG_STATUS        (0x08)       /* CCFG */
#define   LITTLE_ENDIAN_BUS_MODE      (0x0400)    /* Bus in little endian mode */
#define   EEPROM_PRESENCE             (0x0200)    /* External EEPROM is used */
#define   SPI_BUS_MODE                (0x0100)    /* In SPI bus mode */
#define   DATA_BUS_8BIT               (0x0080)    /* In 8-bit bus mode operation */
#define   DATA_BUS_16BIT              (0x0040)    /* In 16-bit bus mode operation */
#define   DATA_BUS_32BIT              (0x0020)    /* In 32-bit bus mode operation */
#define   MULTIPLEX_MODE              (0x0010)    /* Data and address bus are shared */
#define   CHIP_PACKAGE_128PIN         (0x0008)    /* 128-pin package */
#define   CHIP_PACKAGE_80PIN          (0x0004)    /* 80-pin package */
#define   CHIP_PACKAGE_48PIN          (0x0002)    /* 48-pin package */
#define   CHIP_PACKAGE_32PIN          (0x0001)    /* 32-pin package for SPI host interface only */

#define REG_MAC_ADDR_0             (0x10)       /* MARL */
#define REG_MAC_ADDR_1             (0x11)       /* MARL */
#define REG_MAC_ADDR_2             (0x12)       /* MARM */
#define REG_MAC_ADDR_3             (0x13)       /* MARM */
#define REG_MAC_ADDR_4             (0x14)       /* MARH */
#define REG_MAC_ADDR_5             (0x15)       /* MARH */

#define REG_BUS_CLOCK_CTRL         (0x20)       /* OBCR */
#define   BUS_CLOCK_166               (0x0004)    /* 166 MHz on-chip bus clock (defaul is 125MHz) */
#define   BUS_CLOCK_DIVIDEDBY_5       (0x0003)    /* Bus clock devided by 5 */
#define   BUS_CLOCK_DIVIDEDBY_3       (0x0002)    /* Bus clock devided by 3 */
#define   BUS_CLOCK_DIVIDEDBY_2       (0x0001)    /* Bus clock devided by 2 */
#define   BUS_CLOCK_DIVIDEDBY_1       (0x0000)    /* Bus clock devided by 1 */
#define   BUS_CLOCK_DIVIDED_MASK      (0x0003)    /* Bus clock devider mask */

#define   BUS_SPEED_166_MHZ           (0x0004)    /* Set bus speed to 166 MHz */
#define   BUS_SPEED_125_MHZ           (0x0000)    /* Set bus speed to 125 MHz */
#define   BUS_SPEED_83_MHZ            (0x0005)    /* Set bus speed to 83 MHz (166/2)*/
#define   BUS_SPEED_62_5_MHZ          (0x0001)    /* Set bus speed to 62.5 MHz (125/2) */
#define   BUS_SPEED_53_3_MHZ          (0x0006)    /* Set bus speed to 53.3 MHz (166/3) */
#define   BUS_SPEED_41_7_MHZ          (0x0002)    /* Set bus speed to 41.67 MHz (125/3) */
#define   BUS_SPEED_33_2_MHZ          (0x0007)    /* Set bus speed to 33.2 MHz (166/5) */
#define   BUS_SPEED_25_MHZ            (0x0003)    /* Set bus speed to 25 MHz (125/5) */

#define REG_EEPROM_CTRL            (0x22)       /* EEPCR */
#define   EEPROM_ACCESS_ENABLE        (0x0010)    /* Enable software to access EEPROM through bit 3 to bit 0 */
#define   EEPROM_DATA_IN              (0x0008)    /* Data receive from EEPROM (EEDI pin) */
#define   EEPROM_DATA_OUT             (0x0004)    /* Data transmit to EEPROM (EEDO pin) */
#define   EEPROM_SERIAL_CLOCK         (0x0002)    /* Serial clock (EESK pin) */
#define   EEPROM_CHIP_SELECT          (0x0001)    /* EEPROM chip select (EECS pin) */

#define REG_MEM_BIST_INFO          (0x24)       /* MBIR */
#define   TX_MEM_TEST_FINISHED        (0x1000)    /* TX memeory BIST test finish */
#define   TX_MEM_TEST_FAILED          (0x0800)    /* TX memory BIST test fail */
#define   TX_MEM_TEST_FAILED_COUNT    (0x0700)    /* TX memory BIST test fail count */
#define   RX_MEM_TEST_FINISHED        (0x0010)    /* RX memory BIST test finish */
#define   RX_MEM_TEST_FAILED          (0x0008)    /* RX memory BIST test fail */
#define   RX_MEM_TEST_FAILED_COUNT    (0x0003)    /* RX memory BIST test fail count */

#define REG_RESET_CTRL             (0x26)       /* GRR */
#define   QMU_SOFTWARE_RESET          (0x0002)    /* QMU soft reset (clear TxQ, RxQ) */
#define   GLOBAL_SOFTWARE_RESET       (0x0001)    /* Global soft reset (PHY, MAC, QMU) */

/*
 * Wake On Lan Control Registers
 * (Offset 0x2A - 0x6B)
 */
#define REG_WOL_CTRL               (0x2A)       /* WFCR */
#define   WOL_MAGIC_ENABLE            (0x0080)    /* Enable the magic packet pattern detection */
#define   WOL_FRAME3_ENABLE           (0x0008)    /* Enable the wake up frame 3 pattern detection */
#define   WOL_FRAME2_ENABLE           (0x0004)    /* Enable the wake up frame 2 pattern detection */
#define   WOL_FRAME1_ENABLE           (0x0002)    /* Enable the wake up frame 1 pattern detection */
#define   WOL_FRAME0_ENABLE           (0x0001)    /* Enable the wake up frame 0 pattern detection */

#define REG_WOL_FRAME0_CRC0        (0x30)       /* WF0CRC0 */
#define REG_WOL_FRAME0_CRC1        (0x32)       /* WF0CRC1 */
#define REG_WOL_FRAME0_BYTE_MASK0  (0x34)       /* WF0BM0 */
#define REG_WOL_FRAME0_BYTE_MASK1  (0x36)       /* WF0BM1 */
#define REG_WOL_FRAME0_BYTE_MASK2  (0x38)       /* WF0BM2 */
#define REG_WOL_FRAME0_BYTE_MASK3  (0x3A)       /* WF0BM3 */

#define REG_WOL_FRAME1_CRC0        (0x40)       /* WF1CRC0 */
#define REG_WOL_FRAME1_CRC1        (0x42)       /* WF1CRC1 */
#define REG_WOL_FRAME1_BYTE_MASK0  (0x44)       /* WF1BM0 */
#define REG_WOL_FRAME1_BYTE_MASK1  (0x46)       /* WF1BM1 */
#define REG_WOL_FRAME1_BYTE_MASK2  (0x48)       /* WF1BM2 */
#define REG_WOL_FRAME1_BYTE_MASK3  (0x4A)       /* WF1BM3 */

#define REG_WOL_FRAME2_CRC0        (0x50)       /* WF2CRC0 */
#define REG_WOL_FRAME2_CRC1        (0x52)       /* WF2CRC1 */
#define REG_WOL_FRAME2_BYTE_MASK0  (0x54)       /* WF2BM0 */
#define REG_WOL_FRAME2_BYTE_MASK1  (0x56)       /* WF2BM1 */
#define REG_WOL_FRAME2_BYTE_MASK2  (0x58)       /* WF2BM2 */
#define REG_WOL_FRAME2_BYTE_MASK3  (0x5A)       /* WF2BM3 */

#define REG_WOL_FRAME3_CRC0        (0x60)       /* WF3CRC0 */
#define REG_WOL_FRAME3_CRC1        (0x62)       /* WF3CRC1 */
#define REG_WOL_FRAME3_BYTE_MASK0  (0x64)       /* WF3BM0 */
#define REG_WOL_FRAME3_BYTE_MASK1  (0x66)       /* WF3BM1 */
#define REG_WOL_FRAME3_BYTE_MASK2  (0x68)       /* WF3BM2 */
#define REG_WOL_FRAME3_BYTE_MASK3  (0x6A)       /* WF3BM3 */

/*
 * Transmit/Receive Control Registers
 * (Offset 0x70 - 0x9F)
 */

/* Transmit Frame Header */
#define REG_QDR_DUMMY              (0x00)       /* Dummy address to access QMU RxQ, TxQ */
#define   TX_CTRL_INTERRUPT_ON        (0x8000)    /* Transmit Interrupt on Completion */

#define REG_TX_CTRL                (0x70)       /* TXCR */
#define   TX_CTRL_ICMP_CHECKSUM       (0x0100)    /* Enable ICMP frame checksum generation */
#define   TX_CTRL_UDP_CHECKSUM        (0x0080)    /* Enable UDP frame checksum generation */
#define   TX_CTRL_TCP_CHECKSUM        (0x0040)    /* Enable TCP frame checksum generation */
#define   TX_CTRL_IP_CHECKSUM         (0x0020)    /* Enable IP frame checksum generation */
#define   TX_CTRL_FLUSH_QUEUE         (0x0010)    /* Clear transmit queue, reset tx frame pointer */
#define   TX_CTRL_FLOW_ENABLE         (0x0008)    /* Enable transmit flow control */
#define   TX_CTRL_PAD_ENABLE          (0x0004)    /* Eanble adding a padding to a packet shorter than 64 bytes */
#define   TX_CTRL_CRC_ENABLE          (0x0002)    /* Enable adding a CRC to the end of transmit frame */
#define   TX_CTRL_ENABLE              (0x0001)    /* Enable tranmsit */

#define REG_TX_STATUS              (0x72)       /* TXSR */
#define   TX_STAT_LATE_COL            (0x2000)    /* Tranmsit late collision occurs */
#define   TX_STAT_MAX_COL             (0x1000)    /* Tranmsit maximum collision is reached */
#define   TX_FRAME_ID_MASK            (0x003F)    /* Transmit frame ID mask */
#define   TX_STAT_ERRORS             ( TX_STAT_MAX_COL | TX_STAT_LATE_COL )

#define REG_RX_CTRL1               (0x74)       /* RXCR1 */
#define   RX_CTRL_FLUSH_QUEUE         (0x8000)    /* Clear receive queue, reset rx frame pointer */
#define   RX_CTRL_UDP_CHECKSUM        (0x4000)    /* Enable UDP frame checksum verification */
#define   RX_CTRL_TCP_CHECKSUM        (0x2000)    /* Enable TCP frame checksum verification */
#define   RX_CTRL_IP_CHECKSUM         (0x1000)    /* Enable IP frame checksum verification */
#define   RX_CTRL_MAC_FILTER          (0x0800)    /* Receive with address that pass MAC address filtering */
#define   RX_CTRL_FLOW_ENABLE         (0x0400)    /* Enable receive flow control */
#define   RX_CTRL_BAD_PACKET          (0x0200)    /* Eanble receive CRC error frames */
#define   RX_CTRL_MULTICAST           (0x0100)    /* Receive multicast frames that pass the CRC hash filtering */
#define   RX_CTRL_BROADCAST           (0x0080)    /* Receive all the broadcast frames */
#define   RX_CTRL_ALL_MULTICAST       (0x0040)    /* Receive all the multicast frames (including broadcast frames) */
#define   RX_CTRL_UNICAST             (0x0020)    /* Receive unicast frames that match the device MAC address */
#define   RX_CTRL_PROMISCUOUS         (0x0010)    /* Receive all incoming frames, regardless of frame's DA */
#define   RX_CTRL_STRIP_CRC           (0x0008)    /* Enable strip CRC on the received frames */
#define   RX_CTRL_INVERSE_FILTER      (0x0002)    /* Receive with address check in inverse filtering mode */
#define   RX_CTRL_ENABLE              (0x0001)    /* Enable receive */

/* Address filtering scheme mask */
#define RX_CTRL_FILTER_MASK    ( RX_CTRL_INVERSE_FILTER | RX_CTRL_PROMISCUOUS | RX_CTRL_MULTICAST | RX_CTRL_MAC_FILTER )

#define REG_RX_CTRL2               (0x76)       /* RXCR2 */
#define   RX_CTRL_IPV6_UDP_NOCHECKSUM (0x0010)    /* No checksum generation and verification if IPv6 UDP is fragment */
#define   RX_CTRL_IPV6_UDP_CHECKSUM   (0x0008)    /* Receive pass IPv6 UDP frame with UDP checksum is zero */
#define   RX_CTRL_UDP_LITE_CHECKSUM   (0x0004)    /* Enable UDP Lite frame checksum generation and verification */
#define   RX_CTRL_ICMP_CHECKSUM       (0x0002)    /* Enable ICMP frame checksum verification */
#define   RX_CTRL_BLOCK_MAC           (0x0001)    /* Receive drop frame if the SA is same as device MAC address */
#define   RX_CTRL_BURST_LEN_MASK      (0x00e0)    /* SRDBL SPI Receive Data Burst Length */
#define   RX_CTRL_BURST_LEN_4         (0x0000)
#define   RX_CTRL_BURST_LEN_8         (0x0020)
#define   RX_CTRL_BURST_LEN_16        (0x0040)
#define   RX_CTRL_BURST_LEN_32        (0x0060)
#define   RX_CTRL_BURST_LEN_FRAME     (0x0080)

#define REG_TX_MEM_INFO            (0x78)       /* TXMIR */
#define   TX_MEM_AVAILABLE_MASK       (0x1FFF)    /* The amount of memory available in TXQ */

#define REG_RX_FHR_STATUS          (0x7C)       /* RXFHSR */
#define   RX_VALID                    (0x8000)    /* Frame in the receive packet memory is valid */
#define   RX_ICMP_ERROR               (0x2000)    /* ICMP checksum field doesn't match */
#define   RX_IP_ERROR                 (0x1000)    /* IP checksum field doesn't match */
#define   RX_TCP_ERROR                (0x0800)    /* TCP checksum field doesn't match */
#define   RX_UDP_ERROR                (0x0400)    /* UDP checksum field doesn't match */
#define   RX_BROADCAST                (0x0080)    /* Received frame is a broadcast frame */
#define   RX_MULTICAST                (0x0040)    /* Received frame is a multicast frame */
#define   RX_UNICAST                  (0x0020)    /* Received frame is a unicast frame */
#define   RX_PHY_ERROR                (0x0010)    /* Received frame has runt error */
#define   RX_FRAME_ETHER              (0x0008)    /* Received frame is an Ethernet-type frame */
#define   RX_TOO_LONG                 (0x0004)    /* Received frame length exceeds max size 0f 2048 bytes */
#define   RX_RUNT_ERROR               (0x0002)    /* Received frame was demaged by a collision */
#define   RX_BAD_CRC                  (0x0001)    /* Received frame has a CRC error */
#define   RX_ERRORS                   ( RX_BAD_CRC | RX_TOO_LONG | RX_RUNT_ERROR | RX_PHY_ERROR | \
                                        RX_ICMP_ERROR | RX_IP_ERROR | RX_TCP_ERROR | RX_UDP_ERROR )

#define REG_RX_FHR_BYTE_CNT        (0x7E)       /* RXFHBCR */
#define   RX_BYTE_CNT_MASK            (0x0FFF)    /* Received frame byte size mask */

#define REG_TXQ_CMD                (0x80)       /* TXQCR */
#define   TXQ_AUTO_ENQUEUE            (0x0004)    /* Enable enqueue tx frames from tx buffer automatically */
#define   TXQ_MEM_AVAILABLE_INT       (0x0002)    /* Enable generate interrupt when tx memory is available */
#define   TXQ_ENQUEUE                 (0x0001)    /* Enable enqueue tx frames one frame at a time */

#define REG_RXQ_CMD                (0x82)       /* RXQCR */
#define   RXQ_STAT_TIME_INT           (0x1000)    /* RX interrupt is occured by timer duration */
#define   RXQ_STAT_BYTE_CNT_INT       (0x0800)    /* RX interrupt is occured by byte count threshold */
#define   RXQ_STAT_FRAME_CNT_INT      (0x0400)    /* RX interrupt is occured by frame count threshold */
#define   RXQ_TWOBYTE_OFFSET          (0x0200)    /* Enable adding 2-byte before frame header for IP aligned with DWORD */
#define   RXQ_TIME_INT                (0x0080)    /* Enable RX interrupt by timer duration */
#define   RXQ_BYTE_CNT_INT            (0x0040)    /* Enable RX interrupt by byte count threshold */
#define   RXQ_FRAME_CNT_INT           (0x0020)    /* Enable RX interrupt by frame count threshold */
#define   RXQ_AUTO_DEQUEUE            (0x0010)    /* Enable release rx frames from rx buffer automatically */
#define   RXQ_START                   (0x0008)    /* Start QMU transfer operation */
#define   RXQ_CMD_FREE_PACKET         (0x0001)    /* Manual dequeue (release the current frame from RxQ) */

#define   RXQ_CMD_CNTL                (RXQ_FRAME_CNT_INT|RXQ_AUTO_DEQUEUE)

#define REG_TX_ADDR_PTR            (0x84)       /* TXFDPR */
#define REG_RX_ADDR_PTR            (0x86)       /* RXFDPR */
#define   ADDR_PTR_AUTO_INC           (0x4000)    /* Enable Frame data pointer increments automatically */
#define   ADDR_PTR_MASK               (0x03ff)    /* Address pointer mask */

#define REG_RX_TIME_THRES          (0x8C)       /* RXDTTR */
#define   RX_TIME_THRESHOLD_MASK      (0xFFFF)    /* Set receive timer duration threshold */

#define REG_RX_BYTE_CNT_THRES      (0x8E)       /* RXDBCTR */
#define   RX_BYTE_THRESHOLD_MASK      (0xFFFF)    /* Set receive byte count threshold */

#define REG_INT_MASK               (0x90)       /* IER */
#define   INT_PHY                     (0x8000)    /* Enable link change interrupt */
#define   INT_TX                      (0x4000)    /* Enable transmit done interrupt */
#define   INT_RX                      (0x2000)    /* Enable receive interrupt */
#define   INT_RX_OVERRUN              (0x0800)    /* Enable receive overrun interrupt */
#define   INT_TX_STOPPED              (0x0200)    /* Enable transmit process stopped interrupt */
#define   INT_RX_STOPPED              (0x0100)    /* Enable receive process stopped interrupt */
#define   INT_TX_SPACE                (0x0040)    /* Enable transmit space available interrupt */
#define   INT_RX_WOL_FRAME            (0x0020)    /* Enable WOL on receive wake-up frame detect interrupt */
#define   INT_RX_WOL_MAGIC            (0x0010)    /* Enable WOL on receive magic packet detect interrupt */
#define   INT_RX_WOL_LINKUP           (0x0008)    /* Enable WOL on link up detect interrupt */
#define   INT_RX_WOL_ENERGY           (0x0004)    /* Enable WOL on energy detect interrupt */
#define   INT_RX_SPI_ERROR            (0x0002)    /* Enable receive SPI bus error interrupt */
#define   INT_RX_WOL_DELAY_ENERGY     (0x0001)    /* Enable WOL on delay energy detect interrupt */
#define   INT_MASK                    ( INT_RX | INT_TX | INT_PHY )

#define REG_INT_STATUS             (0x92)       /* ISR */

#define REG_RX_FRAME_CNT_THRES     (0x9C)       /* RXFCTFC */
#define   RX_FRAME_CNT_MASK           (0xFF00)    /* Received frame count mask */
#define   RX_FRAME_THRESHOLD_MASK     (0x00FF)    /* Set receive frame count threshold mask */

#define REG_TX_TOTAL_FRAME_SIZE    (0x9E)       /* TXNTFSR */
#define   TX_TOTAL_FRAME_SIZE_MASK    (0xFFFF)    /* Set next total tx frame size mask */

/*
 * MAC Address Hash Table Control Registers
 * (Offset 0xA0 - 0xA7)
 */
#define REG_MAC_HASH_0             (0xA0)       /* MAHTR0 */
#define REG_MAC_HASH_1             (0xA1)

#define REG_MAC_HASH_2             (0xA2)       /* MAHTR1 */
#define REG_MAC_HASH_3             (0xA3)

#define REG_MAC_HASH_4             (0xA4)       /* MAHTR2 */
#define REG_MAC_HASH_5             (0xA5)

#define REG_MAC_HASH_6             (0xA6)       /* MAHTR3 */
#define REG_MAC_HASH_7             (0xA7)

/*
 * QMU Receive Queue Watermark Control Registers
 * (Offset 0xB0 - 0xB5)
 */
#define REG_RX_LOW_WATERMARK       (0xB0)       /* FCLWR */
#define   RX_LOW_WATERMARK_MASK       (0x0FFF)    /* Set QMU RxQ low watermark mask */

#define REG_RX_HIGH_WATERMARK      (0xB2)       /* FCHWR */
#define   RX_HIGH_WATERMARK_MASK      (0x0FFF)    /* Set QMU RxQ high watermark mask */

#define REG_RX_OVERRUN_WATERMARK   (0xB4)       /* FCOWR */
#define   RX_OVERRUN_WATERMARK_MASK   (0x0FFF)    /* Set QMU RxQ overrun watermark mask */

/*
 * Global Control Registers
 * (Offset 0xC0 - 0xD3)
 */
#define REG_CHIP_ID                (0xC0)       /* CIDER */
#define   CHIP_ID_MASK                (0xFFF0)     /* Family ID and chip ID mask */
#define   REVISION_MASK               (0x000E)     /* Chip revision mask */
#define   CHIP_ID_SHIFT               (4)
#define   REVISION_SHIFT              (1)
#define   CHIP_ID_8851_16             (0x8870)     /* KS8851-16/32MQL chip ID */

#define REG_LED_CTRL               (0xC6)       /* CGCR */
#define   LED_CTRL_SEL1               (0x8000)     /* Select LED3/LED2/LED1/LED0 indication */
#define   LED_CTRL_SEL0               (0x0200)     /* Select LED3/LED2/LED1/LED0 indication */

#define REG_IND_IACR               (0xC8)       /* IACR */
#define   TABLE_READ                  (0x1000)     /* Indirect read */
#define   TABLE_MIB                   (0x0C00)     /* Select MIB counter table */
#define   TABLE_ENTRY_MASK            (0x001F)     /* Set table entry to access */

#define REG_IND_DATA_LOW           (0xD0)       /* IADLR */
#define REG_IND_DATA_HIGH          (0xD2)       /* IADHR */

/*
 * Power Management Control Registers
 * (Offset 0xD4 - 0xD7)
 */
#define REG_POWER_CNTL             (0xD4)       /* PMECR */
#define   PME_DELAY_ENABLE            (0x4000)    /* Enable the PME output pin assertion delay */
#define   PME_ACTIVE_HIGHT            (0x1000)    /* PME output pin is active high */
#define   PME_FROM_WKFRAME            (0x0800)    /* PME asserted when wake-up frame is detected */
#define   PME_FROM_MAGIC              (0x0400)    /* PME asserted when magic packet is detected */
#define   PME_FROM_LINKUP             (0x0200)    /* PME asserted when link up is detected */
#define   PME_FROM_ENERGY             (0x0100)    /* PME asserted when energy is detected */
#define   PME_EVENT_MASK              (0x0F00)    /* PME asserted event mask */
#define   WAKEUP_AUTO_ENABLE          (0x0080)    /* Enable auto wake-up in energy mode */
#define   WAKEUP_NORMAL_AUTO_ENABLE   (0x0040)    /* Enable auto goto normal mode from energy detecion mode */
#define   WAKEUP_FROM_WKFRAME         (0x0020)    /* Wake-up from wake-up frame event detected */
#define   WAKEUP_FROM_MAGIC           (0x0010)    /* Wake-up from magic packet event detected */
#define   WAKEUP_FROM_LINKUP          (0x0008)    /* Wake-up from link up event detected */
#define   WAKEUP_FROM_ENERGY          (0x0004)    /* Wake-up from energy event detected */
#define   WAKEUP_EVENT_MASK           (0x003C)    /* Wake-up event mask */
#define   POWER_STATE_D1              (0x0003)    /* Power saving mode */
#define   POWER_STATE_D3              (0x0002)    /* Power down mode */
#define   POWER_STATE_D2              (0x0001)    /* Power detection mode */
#define   POWER_STATE_D0              (0x0000)    /* Normal operation mode (default) */
#define   POWER_STATE_MASK            (0x0003)    /* Power management mode mask */

#define REG_WAKEUP_TIME            (0xD6)       /* GSWUTR */
#define   WAKEUP_TIME                 (0xFF00)    /* Min time (sec) wake-uo after detected energy */
#define   GOSLEEP_TIME                (0x00FF)    /* Min time (sec) before goto sleep when in energy mode */

/*
 * PHY Control Registers
 * (Offset 0xD8 - 0xF9)
 */
#define REG_PHY_RESET              (0xD8)       /* PHYRR */
#define   PHY_RESET                   (0x0001)    /* Reset PHY */

#define REG_PHY_CNTL               (0xE4)       /* P1MBCR */
#define   PHY_SPEED_100MBIT           (0x2000)     /* Force PHY 100Mbps */
#define   PHY_AUTO_NEG_ENABLE         (0x1000)     /* Enable PHY auto-negotiation */
#define   PHY_POWER_DOWN              (0x0800)     /* Set PHY power-down */
#define   PHY_AUTO_NEG_RESTART        (0x0200)     /* Restart PHY auto-negotiation */
#define   PHY_FULL_DUPLEX             (0x0100)     /* Force PHY in full duplex mode */
#define   PHY_HP_MDIX                 (0x0020)     /* Set PHY in HP auto MDI-X mode */
#define   PHY_FORCE_MDIX              (0x0010)     /* Force MDI-X */
#define   PHY_AUTO_MDIX_DISABLE       (0x0008)     /* Disable auto MDI-X */
#define   PHY_TRANSMIT_DISABLE        (0x0002)     /* Disable PHY transmit */
#define   PHY_LED_DISABLE             (0x0001)     /* Disable PHY LED */

#define REG_PHY_STATUS             (0xE6)       /* P1MBSR */
#define   PHY_100BT4_CAPABLE          (0x8000)     /* 100 BASE-T4 capable */
#define   PHY_100BTX_FD_CAPABLE       (0x4000)     /* 100BASE-TX full duplex capable */
#define   PHY_100BTX_CAPABLE          (0x2000)     /* 100BASE-TX half duplex capable */
#define   PHY_10BT_FD_CAPABLE         (0x1000)     /* 10BASE-TX full duplex capable */
#define   PHY_10BT_CAPABLE            (0x0800)     /* 10BASE-TX half duplex capable */
#define   PHY_AUTO_NEG_ACKNOWLEDGE    (0x0020)     /* Auto-negotiation complete */
#define   PHY_AUTO_NEG_CAPABLE        (0x0008)     /* Auto-negotiation capable */
#define   PHY_LINK_UP                 (0x0004)     /* PHY link is up */
#define   PHY_EXTENDED_CAPABILITY     (0x0001)     /* PHY extended register capable */

#define REG_PHY_ID_LOW             (0xE8)       /* PHY1ILR */
#define REG_PHY_ID_HIGH            (0xEA)       /* PHY1IHR */

#define REG_PHY_AUTO_NEGOTIATION   (0xEC)       /* P1ANAR */
#define   PHY_AUTO_NEG_SYM_PAUSE      (0x0400)     /* Advertise pause capability */
#define   PHY_AUTO_NEG_100BTX_FD      (0x0100)     /* Advertise 100 full-duplex capability */
#define   PHY_AUTO_NEG_100BTX         (0x0080)     /* Advertise 100 half-duplex capability */
#define   PHY_AUTO_NEG_10BT_FD        (0x0040)     /* Advertise 10 full-duplex capability */
#define   PHY_AUTO_NEG_10BT           (0x0020)     /* Advertise 10 half-duplex capability */
#define   PHY_AUTO_NEG_SELECTOR       (0x001F)     /* Selector field mask */
#define   PHY_AUTO_NEG_802_3          (0x0001)     /* 802.3 */

#define REG_PHY_REMOTE_CAPABILITY  (0xEE)       /* P1ANLPR */
#define   PHY_REMOTE_SYM_PAUSE        (0x0400)     /* Link partner pause capability */
#define   PHY_REMOTE_100BTX_FD        (0x0100)     /* Link partner 100 full-duplex capability */
#define   PHY_REMOTE_100BTX           (0x0080)     /* Link partner 100 half-duplex capability */
#define   PHY_REMOTE_10BT_FD          (0x0040)     /* Link partner 10 full-duplex capability */
#define   PHY_REMOTE_10BT             (0x0020)     /* Link partner 10 half-duplex capability */

#define REG_PORT_LINK_MD           (0xF4)       /* P1SCLMD */
#define   PORT_CABLE_10M_SHORT        (0x8000)     /* Cable length is less than 10m short */
#define   PORT_CABLE_STAT_FAILED      (0x6000)     /* Cable diagnostic test fail */
#define   PORT_CABLE_STAT_SHORT       (0x4000)     /* Short condition detected in the cable */
#define   PORT_CABLE_STAT_OPEN        (0x2000)     /* Open condition detected in the cable */
#define   PORT_CABLE_STAT_NORMAL      (0x0000)     /* Normal condition */
#define   PORT_CABLE_DIAG_RESULT      (0x6000)     /* Cable diagnostic test result mask */
#define   PORT_START_CABLE_DIAG       (0x1000)     /* Enable cable diagnostic test */
#define   PORT_FORCE_LINK             (0x0800)     /* Enable force link pass */
#define   PORT_POWER_SAVING           (0x0400)     /* Disable power saving */
#define   PORT_REMOTE_LOOPBACK        (0x0200)     /* Enable remote loopback at PHY */
#define   PORT_CABLE_FAULT_COUNTER    (0x01FF)     /* Cable length distance to the fault */

#define REG_PORT_CTRL              (0xF6)       /* P1CR */
#define   PORT_LED_OFF                (0x8000)     /* Turn off all the port LEDs (LED3/LED2/LED1/LED0) */
#define   PORT_TX_DISABLE             (0x4000)     /* Disable port transmit */
#define   PORT_AUTO_NEG_RESTART       (0x2000)     /* Restart auto-negotiation */
#define   PORT_POWER_DOWN             (0x0800)     /* Set port power-down */
#define   PORT_AUTO_MDIX_DISABLE      (0x0400)     /* Disable auto MDI-X */
#define   PORT_FORCE_MDIX             (0x0200)     /* Force MDI-X */
#define   PORT_AUTO_NEG_ENABLE        (0x0080)     /* Enable auto-negotiation */
#define   PORT_FORCE_100_MBIT         (0x0040)     /* Force PHY 100Mbps */
#define   PORT_FORCE_FULL_DUPLEX      (0x0020)     /* Force PHY in full duplex mode */
#define   PORT_AUTO_NEG_SYM_PAUSE     (0x0010)     /* Advertise pause capability */
#define   PORT_AUTO_NEG_100BTX_FD     (0x0008)     /* Advertise 100 full-duplex capability */
#define   PORT_AUTO_NEG_100BTX        (0x0004)     /* Advertise 100 half-duplex capability */
#define   PORT_AUTO_NEG_10BT_FD       (0x0002)     /* Advertise 10 full-duplex capability */
#define   PORT_AUTO_NEG_10BT          (0x0001)     /* Advertise 10 half-duplex capability */

#define REG_PORT_STATUS            (0xF8)       /* P1SR */
#define   PORT_HP_MDIX                (0x8000)     /* Set PHY in HP auto MDI-X mode */
#define   PORT_REVERSED_POLARITY      (0x2000)     /* Polarity is reversed */
#define   PORT_RX_FLOW_CTRL           (0x1000)     /* Reeive flow control feature is active */
#define   PORT_TX_FLOW_CTRL           (0x0800)     /* Transmit flow control feature is active */
#define   PORT_STAT_SPEED_100MBIT     (0x0400)     /* Link is 100Mbps */
#define   PORT_STAT_FULL_DUPLEX       (0x0200)     /* Link is full duplex mode */
#define   PORT_MDIX_STATUS            (0x0080)     /* Is MDI */
#define   PORT_AUTO_NEG_COMPLETE      (0x0040)     /* Auto-negotiation complete */
#define   PORT_STATUS_LINK_GOOD       (0x0020)     /* PHY link is up */
#define   PORT_REMOTE_SYM_PAUSE       (0x0010)     /* Link partner pause capability */
#define   PORT_REMOTE_100BTX_FD       (0x0008)     /* Link partner 100 full-duplex capability */
#define   PORT_REMOTE_100BTX          (0x0004)     /* Link partner 100 half-duplex capability */
#define   PORT_REMOTE_10BT_FD         (0x0002)     /* Link partner 10 full-duplex capability */
#define   PORT_REMOTE_10BT            (0x0001)     /* Link partner 10 half-duplex capability */

#endif /* KSZ8851SNL_REG_H_INCLUDED */
