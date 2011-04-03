/***************************************************************************//**
 * @file
 * SmartFusion MSS Ethernet MAC registers.
 *
 * (c) Copyright 2007 Actel Corporation
 *
 * IP core registers definitions. This file contains the definitions required
 * for accessing the IP core through the hardware abstraction layer (HAL).
 * This file was automatically generated, using "get_header.exe" version 0.4.0,
 * from the IP-XACT description for:
 *
 *
 * SVN $Revision: 2364 $
 * SVN $Date: 2010-03-01 17:58:41 +0000 (Mon, 01 Mar 2010) $
 *
 *******************************************************************************/
#ifndef MSS_ETHERNET_MAC_REGISTERS_H_
#define MSS_ETHERNET_MAC_REGISTERS_H_

#ifdef __cplusplus
extern "C" {
#endif 

#include "../../CMSIS/a2fxxxm3.h"
#include "mss_ethernet_mac.h"
#include "mss_ethernet_mac_user_cfg.h"
  
typedef uint32_t addr_t;


/***************************************************************************//**
 * Descriptor structure
 */
typedef struct {
    volatile uint32_t   descriptor_0;
    volatile uint32_t   descriptor_1;
    volatile uint32_t   buffer_1;
    volatile uint32_t   buffer_2;
} MAC_descriptor_t;


/***************************************************************************//**
 * There should be one instance of this structure for each instance of
 * the MAC in your system. MSS_MAC_init routine initializes this structure.
 * It is used to identify the various MACs in your system and an initilized 
 * MAC instance's structure should be passed as first parameter to MAC functions 
 * to identify which MAC should perform the requested operation.
 * Software using the MAC driver should only need to create one single 
 * instance of this data structure for each MAC hardware instance in 
 * the system. Using MAC_get_configuration routine, latest status of the driver
 * may be read by receiving its flags field, similarly MAC_configure routine lets
 * you modify some of these flags.
 */
typedef struct {
	addr_t		base_address;           /**< Register base address of the driver*/
    uint8_t		flags;                  /**< Configuration of the driver*/
    int8_t		last_error;             /**< Index of last error happened inside the driver*/
    uint8_t     mac_address[6];			/**< MAC address of the drived instance*/
    uint8_t     mac_filter_data[90];	/**< MAC filter data, 15 addresses to be used for 
                                            received data filtering*/
    uint16_t	last_timer_value;		/**< Last read value of timer */
    uint32_t	time_out_value;			/**< Time out value */
    MSS_MAC_callback_t listener;            /**< Pointer to the call-back function to be triggered 
                                            when a package is received*/

	/* transmit related info: */
    uint32_t    tx_desc_index;          /**< index of the transmit descriptor getting used*/
    uint8_t     tx_buffers[TX_RING_SIZE][MSS_TX_BUFF_SIZE];/**< array of transmit buffers*/
    MAC_descriptor_t tx_descriptors[TX_RING_SIZE];/**< array of transmit descriptors*/

	/* receive related info: */
    uint32_t    rx_desc_index;          /**< index of the receive descriptor getting used*/
    uint8_t     rx_buffers[RX_RING_SIZE][MSS_RX_BUFF_SIZE+4];/**< array of receive buffers*/
    MAC_descriptor_t rx_descriptors[RX_RING_SIZE];/**< array of receive descriptors*/
    
    uint8_t		phy_address;            /**< MII address of the connected PHY*/
    
	struct {
		uint32_t rx_interrupts;			/**< Number of receive interrupts occurred.*/
		uint32_t rx_filtering_fail;		/**< Number of received frames which did not pass 
											the address recognition process.*/
		uint32_t rx_descriptor_error;	/**< Number of occurrences of; no receive buffer was
											available when trying to store the received data.*/
		uint32_t rx_runt_frame;			/**< Number of occurrences of; the frame is damaged by 
											a collision or by a premature termination before 
											the end of a collision window.*/
		uint32_t rx_not_first;			/**< Number of occurrences of; start of the frame is 
											not the first descriptor of a frame.*/
		uint32_t rx_not_last;			/**< Number of occurrences of; end of the frame is not 
											the first descriptor of a frame.*/
		uint32_t rx_frame_too_long;		/**< Number of occurrences of; a current frame is 
											longer than maximum size of 1,518 bytes, as specified 
											by 802.3.*/
		uint32_t rx_collision_seen;		/**< Number of occurrences of; a late collision was seen 
											(collision after 64 bytes following SFD).*/
		uint32_t rx_crc_error;			/**< Number of occurrences of; a CRC error has occurred 
											in the received frame.*/
		uint32_t rx_fifo_overflow;		/**< Number of frames not accepted due to the receive 
											FIFO overflow.*/
		uint32_t rx_missed_frame;		/**< Number of frames not accepted due to the 
											unavailability of the receive descriptor.*/
		
		uint32_t tx_interrupts;			/**< Number of transmit interrupts occurred.*/
		uint32_t tx_loss_of_carrier;	/**< Number of occurrences of; a loss of the carrier 
											during a transmission.*/
		uint32_t tx_no_carrier;			/**< Number of occurrences of; the carrier was not asserted
											by an external transceiver during the transmission.*/
		uint32_t tx_late_collision;		/**< Number of occurrences of; a collision was detected 
											after transmitting 64 bytes.*/
		uint32_t tx_excessive_collision;/**< Number of occurrences of; the transmission was 
											aborted after 16 retries.*/
		uint32_t tx_collision_count;	/**< Number of collisions occurred.*/
		uint32_t tx_underflow_error;	/**< Number of occurrences of; the FIFO was empty during 
											the frame transmission.*/
    } statistics;
} MAC_instance_t;


/*------------------------------------------------------------------------------
 *
 */
typedef struct
{
    uint32_t CSR0_SWR;
    uint32_t CSR0_BAR;
    uint32_t CSR0_DSL[5];
    uint32_t CSR0_BLE;
    uint32_t CSR0_PBL[6];
    uint32_t CSR0_RESERVED0[3];
    uint32_t CSR0_TAP[3];
    uint32_t CSR0_DBO;
    uint32_t CSR0_RESERVED1[11];
    
    uint32_t MAC_CSR_RESERVED0[32];
    
    uint32_t CSR1[32];
    
    uint32_t MAC_CSR_RESERVED1[32];
    
    uint32_t CSR2[32];
    
    uint32_t MAC_CSR_RESERVED2[32];
    
    uint32_t CSR3[32];
    
    uint32_t MAC_CSR_RESERVED3[32];
    
    uint32_t CSR4[32];
    
    uint32_t MAC_CSR_RESERVED4[32];
    
    uint32_t CSR5_TI;
    uint32_t CSR5_TPS;
    uint32_t CSR5_TU;
    uint32_t CSR5_RESERVED0[2];    
    uint32_t CSR5_UNF;
    uint32_t CSR5_RI;
    uint32_t CSR5_RU;
    uint32_t CSR5_RPS;
    uint32_t CSR5_RESERVED1;
    uint32_t CSR5_ETI;
    uint32_t CSR5_GTE;
    uint32_t CSR5_RESERVED2[2];
    uint32_t CSR5_ERI;
    uint32_t CSR5_AIS;
    uint32_t CSR5_NIS;
    uint32_t CSR5_RS[3];
    uint32_t CSR5_TS[3];
    uint32_t CSR5_RESERVED3[9];

    uint32_t MAC_CSR_RESERVED5[32];
    
    uint32_t CSR6_HP;
    uint32_t CSR6_SR;
    uint32_t CSR6_HO;
    uint32_t CSR6_PB;
    uint32_t CSR6_IF;
    uint32_t CSR6_RESERVED0;
    uint32_t CSR6_PR;
    uint32_t CSR6_PM;
    uint32_t CSR6_RESERVED1;
    uint32_t CSR6_FD;
    uint32_t CSR6_RESERVED2[3];
    uint32_t CSR6_ST;
    uint32_t CSR6_TR[2];
    uint32_t CSR6_RESERVED3[5];
    uint32_t CSR6_SF;
    uint32_t CSR6_TTM;
    uint32_t CSR6_RESERVED4[7];
    uint32_t CSR6_RA;
    uint32_t CSR6_RESERVED5;

    uint32_t MAC_CSR_RESERVED6[32];
    
    uint32_t CSR7_TIE;
    uint32_t CSR7_TSE;
    uint32_t CSR7_TUE;
    uint32_t CSR7_RESERVED0[2];
    uint32_t CSR7_UNE;
    uint32_t CSR7_RIE;
    uint32_t CSR7_RUE;
    uint32_t CSR7_RSE;
    uint32_t CSR7_RESERVED1;
    uint32_t CSR7_ETE;
    uint32_t CSR7_GTE;
    uint32_t CSR7_RESERVED2[2];
    uint32_t CSR7_ERE;
    uint32_t CSR7_AIE;
    uint32_t CSR7_NIE;
    uint32_t CSR7[15];

    uint32_t MAC_CSR_RESERVED7[32];
    
    uint32_t CSR8[32];

    uint32_t MAC_CSR_RESERVED8[32];
    
    uint32_t CSR9_SCS;
    uint32_t CSR9_SCLK;
    uint32_t CSR9_SDI;
    uint32_t CSR9_SDO;
    uint32_t CSR9_RESERVED0[12];
    uint32_t CSR9_MDC;
    uint32_t CSR9_MDO;
    uint32_t CSR9_MDEN;
    uint32_t CSR9_MDI;
    uint32_t CSR9_RESERVED1[12];

    uint32_t MAC_CSR_RESERVED9[32];
    
    uint32_t CSR10[32];

    uint32_t MAC_CSR_RESERVED10[32];
    
    uint32_t CSR11_TIM[16];
    uint32_t CSR11_CON;
    uint32_t CSR11_NRP[3];
    uint32_t CSR11_RT[4];
    uint32_t CSR11_NTP[3];
    uint32_t CSR11_TT[4];
    uint32_t CSR11_CS;
} MAC_BitBand_TypeDef;

#define MAC_BITBAND   ((MAC_BitBand_TypeDef *) BITBAND_ADDRESS(MAC_BASE))

/*******************************************************************************
 * CSR0 register:
 *------------------------------------------------------------------------------
 * CSR0 - Bus Mode Register
 */
#define CSR0_REG_OFFSET	0x00

/*------------------------------------------------------------------------------
 * CSR0_DBO:
 *   DBO field of register CSR0.
 *------------------------------------------------------------------------------
 * Descriptor byte ordering mode
 */
#define CSR0_DBO_OFFSET   0x00
#define CSR0_DBO_MASK     0x00100000UL
#define CSR0_DBO_SHIFT    20

/*
 * Allowed values for CSR0_DBO:
 *------------------------------------------------------------------------------
 * LITTLEENDIAN:   Little endian mode used for data descriptors
 * BIGENDIAN:      Big endian mode used for data descriptors
 */
#define LITTLEENDIAN    0u
#define BIGENDIAN       1u

/*------------------------------------------------------------------------------
 * CSR0_TAP:
 *   TAP field of register CSR0.
 *------------------------------------------------------------------------------
 * Transmit automatic polling
 */
#define CSR0_TAP_OFFSET   0x00
#define CSR0_TAP_MASK     0x000E0000UL
#define CSR0_TAP_SHIFT    17

/*
 * Allowed values for CSR0_TAP:
 *------------------------------------------------------------------------------
 * TAP_DISABLED:   TAP disabled
 * TAP_819US:      TAP 819/81.9us
 * TAP_2450US:     TAP 2450/245us
 * TAP_5730US:     TAP 5730/573us
 * TAP_51_2US:     TAP 51.2/5.12us
 * TAP_102_4US:    TAP 102.4/10.24us
 * TAP_153_6US:    TAP 156.6/15.26us
 * TAP_358_4US:    TAP 358.4/35.84us
 */
#define TAP_DISABLED    0x0
#define TAP_819US       0x1
#define TAP_2450US      0x2
#define TAP_5730US      0x3
#define TAP_51_2US      0x4
#define TAP_102_4US     0x5
#define TAP_153_6US     0x6
#define TAP_358_4US     0x7

/*------------------------------------------------------------------------------
 * CSR0_PBL:
 *   PBL field of register CSR0.
 *------------------------------------------------------------------------------
 * Programmable burst length
 */
#define CSR0_PBL_OFFSET   0x00
#define CSR0_PBL_MASK     0x00003F00uL
#define CSR0_PBL_SHIFT    8

/*------------------------------------------------------------------------------
 * CSR0_BLE:
 *   BLE field of register CSR0.
 *------------------------------------------------------------------------------
 * Big/little endian
 */
#define CSR0_BLE_OFFSET   0x00
#define CSR0_BLE_MASK     0x00000080uL
#define CSR0_BLE_SHIFT    7

/*------------------------------------------------------------------------------
 * CSR0_DSL:
 *   DSL field of register CSR0.
 *------------------------------------------------------------------------------
 * Descriptor skip length
 */
#define CSR0_DSL_OFFSET   0x00
#define CSR0_DSL_MASK     0x0000007CuL
#define CSR0_DSL_SHIFT    2

/*------------------------------------------------------------------------------
 * CSR0_BAR:
 *   BAR field of register CSR0.
 *------------------------------------------------------------------------------
 * Bus arbitration scheme
 */
#define CSR0_BAR_OFFSET   0x00
#define CSR0_BAR_MASK     0x00000002uL
#define CSR0_BAR_SHIFT    1

/*------------------------------------------------------------------------------
 * CSR0_SWR:
 *   SWR field of register CSR0.
 *------------------------------------------------------------------------------
 * Software reset
 */
#define CSR0_SWR_OFFSET   0x00
#define CSR0_SWR_MASK     0x00000001uL
#define CSR0_SWR_SHIFT    0

/*******************************************************************************
 * CSR1 register:
 *------------------------------------------------------------------------------
 * CSR1 - Transmit Poll Demand Register
 */
#define CSR1_REG_OFFSET	0x08

/*------------------------------------------------------------------------------
 * CSR1_TPD3:
 *   TPD3 field of register CSR1.
 *------------------------------------------------------------------------------
 * TPD(31..24)
 */
#define CSR1_TPD3_OFFSET   0x08
#define CSR1_TPD3_MASK     0xFF000000uL
#define CSR1_TPD3_SHIFT    24

/*------------------------------------------------------------------------------
 * CSR1_TPD2:
 *   TPD2 field of register CSR1.
 *------------------------------------------------------------------------------
 * TPD(23..16)
 */
#define CSR1_TPD2_OFFSET   0x08
#define CSR1_TPD2_MASK     0x00FF0000uL
#define CSR1_TPD2_SHIFT    16

/*------------------------------------------------------------------------------
 * CSR1_TPD1:
 *   TPD1 field of register CSR1.
 *------------------------------------------------------------------------------
 * TPD(15..8)
 */
#define CSR1_TPD1_OFFSET   0x08
#define CSR1_TPD1_MASK     0x0000FF00uL
#define CSR1_TPD1_SHIFT    8

/*------------------------------------------------------------------------------
 * CSR1_TPD0:
 *   TPD0 field of register CSR1.
 *------------------------------------------------------------------------------
 * TPD(7..0)
 */
#define CSR1_TPD0_OFFSET   0x08
#define CSR1_TPD0_MASK     0x000000FFuL
#define CSR1_TPD0_SHIFT    0

/*******************************************************************************
 * CSR2 register:
 *------------------------------------------------------------------------------
 * CSR2 - Receive Poll Demand Register
 */
#define CSR2_REG_OFFSET	0x10

/*------------------------------------------------------------------------------
 * CSR2_RPD3:
 *   RPD3 field of register CSR2.
 *------------------------------------------------------------------------------
 * RPD(31..24)
 */
#define CSR2_RPD3_OFFSET   0x10
#define CSR2_RPD3_MASK     0xFF000000uL
#define CSR2_RPD3_SHIFT    24

/*------------------------------------------------------------------------------
 * CSR2_RPD2:
 *   RPD2 field of register CSR2.
 *------------------------------------------------------------------------------
 * RPD(23..16)
 */
#define CSR2_RPD2_OFFSET   0x10
#define CSR2_RPD2_MASK     0x00FF0000uL
#define CSR2_RPD2_SHIFT    16

/*------------------------------------------------------------------------------
 * CSR2_RPD1:
 *   RPD1 field of register CSR2.
 *------------------------------------------------------------------------------
 * RPD(15..8)
 */
#define CSR2_RPD1_OFFSET   0x10
#define CSR2_RPD1_MASK     0x0000FF00uL
#define CSR2_RPD1_SHIFT    8

/*------------------------------------------------------------------------------
 * CSR2_RPD0:
 *   RPD0 field of register CSR2.
 *------------------------------------------------------------------------------
 * RPD(7..0)
 */
#define CSR2_RPD0_OFFSET   0x10
#define CSR2_RPD0_MASK     0x000000FFuL
#define CSR2_RPD0_SHIFT    0

/*******************************************************************************
 * CSR3 register:
 *------------------------------------------------------------------------------
 * CSR3 - Receive Descriptor List Base Address Register
 */
#define CSR3_REG_OFFSET	0x18

/*------------------------------------------------------------------------------
 * CSR3_RLA3:
 *   RLA3 field of register CSR3.
 *------------------------------------------------------------------------------
 * RLA(31..24)
 */
#define CSR3_RLA3_OFFSET   0x18
#define CSR3_RLA3_MASK     0xFF000000uL
#define CSR3_RLA3_SHIFT    24

/*------------------------------------------------------------------------------
 * CSR3_RLA2:
 *   RLA2 field of register CSR3.
 *------------------------------------------------------------------------------
 * RLA(23..16)
 */
#define CSR3_RLA2_OFFSET   0x18
#define CSR3_RLA2_MASK     0x00FF0000uL
#define CSR3_RLA2_SHIFT    16

/*------------------------------------------------------------------------------
 * CSR3_RLA1:
 *   RLA1 field of register CSR3.
 *------------------------------------------------------------------------------
 * RLA(15..8)
 */
#define CSR3_RLA1_OFFSET   0x18
#define CSR3_RLA1_MASK     0x0000FF00uL
#define CSR3_RLA1_SHIFT    8

/*------------------------------------------------------------------------------
 * CSR3_RLA0:
 *   RLA0 field of register CSR3.
 *------------------------------------------------------------------------------
 * RLA(7..0)
 */
#define CSR3_RLA0_OFFSET   0x18
#define CSR3_RLA0_MASK     0x000000FFuL
#define CSR3_RLA0_SHIFT    0

/*******************************************************************************
 * CSR4 register:
 *------------------------------------------------------------------------------
 * CSR4 - Transmit Descriptor List Base Address Register
 */
#define CSR4_REG_OFFSET	0x20

/*------------------------------------------------------------------------------
 * CSR4_TLA3:
 *   TLA3 field of register CSR4.
 *------------------------------------------------------------------------------
 * TLA(31..24)
 */
#define CSR4_TLA3_OFFSET   0x20
#define CSR4_TLA3_MASK     0xFF000000uL
#define CSR4_TLA3_SHIFT    24

/*------------------------------------------------------------------------------
 * CSR4_TLA2:
 *   TLA2 field of register CSR4.
 *------------------------------------------------------------------------------
 * TLA(23..16)
 */
#define CSR4_TLA2_OFFSET   0x20
#define CSR4_TLA2_MASK     0x00FF0000uL
#define CSR4_TLA2_SHIFT    16

/*------------------------------------------------------------------------------
 * CSR4_TLA1:
 *   TLA1 field of register CSR4.
 *------------------------------------------------------------------------------
 * TLA(15..8)
 */
#define CSR4_TLA1_OFFSET   0x20
#define CSR4_TLA1_MASK     0x0000FF00uL
#define CSR4_TLA1_SHIFT    8

/*------------------------------------------------------------------------------
 * CSR4_TLA0:
 *   TLA0 field of register CSR4.
 *------------------------------------------------------------------------------
 * TLA(7..0)
 */
#define CSR4_TLA0_OFFSET   0x20
#define CSR4_TLA0_MASK     0x000000FFuL
#define CSR4_TLA0_SHIFT    0

/*******************************************************************************
 * CSR5 register:
 *------------------------------------------------------------------------------
 * CSR5 - Status Register
 */
#define CSR5_REG_OFFSET	0x28
#define CSR5_INT_BITS	(CSR5_NIS_MASK | CSR5_AIS_MASK | CSR5_ERI_MASK | \
	CSR5_GTE_MASK | CSR5_ETI_MASK | CSR5_RPS_MASK | CSR5_RU_MASK | \
	CSR5_RI_MASK | CSR5_UNF_MASK | CSR5_TU_MASK | CSR5_TPS_MASK | CSR5_TI_MASK)

/*------------------------------------------------------------------------------
 * CSR5_TS:
 *   TS field of register CSR5.
 *------------------------------------------------------------------------------
 * Transmit process state
 */
#define CSR5_TS_OFFSET   0x28
#define CSR5_TS_MASK     0x00700000uL
#define CSR5_TS_SHIFT    20

/** 000 - Stopped; RESET or STOP TRANSMIT command issued.             */
#define CSR5_TS_STOPPED    0u 
/** 001 - Running, fetching the transmit descriptor.                  */
#define CSR5_TS_RUNNING_FD 1u 
/** 010 - Running, waiting for end of transmission.                   */
#define CSR5_TS_RUNNING_WT 2u 
/** 011 - Running, transferring data buffer from host memory to FIFO. */
#define CSR5_TS_RUNNING_TD 3u 
/** 101 - Running, setup packet.                                      */
#define CSR5_TS_RUNNING_SP 5u 
/** 110 - Suspended; FIFO underflow or unavailable descriptor.        */
#define CSR5_TS_SUSPENDED  6u 
/** 111 - Running, closing transmit descriptor.                       */
#define CSR5_TS_RUNNING_CD 7u 

/*------------------------------------------------------------------------------
 * CSR5_RS:
 *   RS field of register CSR5.
 *------------------------------------------------------------------------------
 * Receive process state
 */
#define CSR5_RS_OFFSET   0x28
#define CSR5_RS_MASK     0x00060000uL
#define CSR5_RS_SHIFT    17

/** 000 - Stopped; RESET or STOP RECEIVE command issued.                      */
#define CSR5_RS_STOPPED    0u                                                  
/** 001 - Running, fetching the receive descriptor.                           */
#define CSR5_RS_RUNNING_FD 1u                                                  
/** 010 - Running, waiting for the end-of-receive packet before prefetch of the
 *next descriptor. */                                                         
#define CSR5_RS_RUNNING_WR 2u                                                  
/** 011 - Running, waiting for the receive packet.                            */
#define CSR5_RS_RUNNING_RB 3u                                                  
/** 100 - Suspended, unavailable receive buffer.                              */
#define CSR5_RS_SUSPENDED  4u                                                  
/** 101 - Running, closing the receive descriptor.                            */
#define CSR5_RS_RUNNING_CD 5u                                                  
/** 111 - Running, transferring data from FIFO to host memory.                */                                                                                                                     
#define CSR5_RS_RUNNING_TD 7u

/*------------------------------------------------------------------------------
 * CSR5_NIS:
 *   NIS field of register CSR5.
 *------------------------------------------------------------------------------
 * Normal interrupt summary
 */
#define CSR5_NIS_OFFSET   0x28
#define CSR5_NIS_MASK     0x00010000uL
#define CSR5_NIS_SHIFT    16

/*------------------------------------------------------------------------------
 * CSR5_AIS:
 *   AIS field of register CSR5.
 *------------------------------------------------------------------------------
 * Abnormal interrupt summary
 */
#define CSR5_AIS_OFFSET   0x28
#define CSR5_AIS_MASK     0x00008000UL
#define CSR5_AIS_SHIFT    15

/*------------------------------------------------------------------------------
 * CSR5_ERI:
 *   ERI field of register CSR5.
 *------------------------------------------------------------------------------
 * Early receive interrupt
 */
#define CSR5_ERI_OFFSET   0x28
#define CSR5_ERI_MASK     0x00004000UL
#define CSR5_ERI_SHIFT    14

/*------------------------------------------------------------------------------
 * CSR5_GTE:
 *   GTE field of register CSR5.
 *------------------------------------------------------------------------------
 * General-purpose timer expiration
 */
#define CSR5_GTE_OFFSET   0x28
#define CSR5_GTE_MASK     0x00000800UL
#define CSR5_GTE_SHIFT    11

/*------------------------------------------------------------------------------
 * CSR5_ETI:
 *   ETI field of register CSR5.
 *------------------------------------------------------------------------------
 * Early transmit interrupt
 */
#define CSR5_ETI_OFFSET   0x28
#define CSR5_ETI_MASK     0x00000400UL
#define CSR5_ETI_SHIFT    10

/*------------------------------------------------------------------------------
 * CSR5_RPS:
 *   RPS field of register CSR5.
 *------------------------------------------------------------------------------
 * Receive process stopped
 */
#define CSR5_RPS_OFFSET   0x28
#define CSR5_RPS_MASK     0x00000100UL
#define CSR5_RPS_SHIFT    8

/*------------------------------------------------------------------------------
 * CSR5_RU:
 *   RU field of register CSR5.
 *------------------------------------------------------------------------------
 * Receive buffer unavailable
 */
#define CSR5_RU_OFFSET   0x28
#define CSR5_RU_MASK     0x00000080UL
#define CSR5_RU_SHIFT    7

/*------------------------------------------------------------------------------
 * CSR5_RI:
 *   RI field of register CSR5.
 *------------------------------------------------------------------------------
 * Receive interrupt
 */
#define CSR5_RI_OFFSET   0x28
#define CSR5_RI_MASK     0x00000040UL
#define CSR5_RI_SHIFT    6

/*------------------------------------------------------------------------------
 * CSR5_UNF:
 *   UNF field of register CSR5.
 *------------------------------------------------------------------------------
 * Transmit underflow
 */
#define CSR5_UNF_OFFSET   0x28
#define CSR5_UNF_MASK     0x00000020UL
#define CSR5_UNF_SHIFT    5

/*------------------------------------------------------------------------------
 * CSR5_TU:
 *   TU field of register CSR5.
 *------------------------------------------------------------------------------
 * Transmit buffer unavailable
 */
#define CSR5_TU_OFFSET   0x28
#define CSR5_TU_MASK     0x00000004UL
#define CSR5_TU_SHIFT    2

/*------------------------------------------------------------------------------
 * CSR5_TPS:
 *   TPS field of register CSR5.
 *------------------------------------------------------------------------------
 * Transmit process stopped
 */
#define CSR5_TPS_OFFSET   0x28
#define CSR5_TPS_MASK     0x00000002UL
#define CSR5_TPS_SHIFT    1

/*------------------------------------------------------------------------------
 * CSR5_TI:
 *   TI field of register CSR5.
 *------------------------------------------------------------------------------
 * Transmit interrupt
 */
#define CSR5_TI_OFFSET   0x28
#define CSR5_TI_MASK     0x00000001UL
#define CSR5_TI_SHIFT    0

/*******************************************************************************
 * CSR6 register:
 *------------------------------------------------------------------------------
 * CSR6 - Operation Mode Register
 */
#define CSR6_REG_OFFSET	0x30

/*------------------------------------------------------------------------------
 * CSR6_RA:
 *   RA field of register CSR6.
 *------------------------------------------------------------------------------
 * Receive all
 */
#define CSR6_RA_OFFSET   0x30
#define CSR6_RA_MASK     0x40000000UL
#define CSR6_RA_SHIFT    30

/*------------------------------------------------------------------------------
 * CSR6_TTM:
 *   TTM field of register CSR6.
 *------------------------------------------------------------------------------
 * Transmit threshold mode
 */
#define CSR6_TTM_OFFSET   0x30
#define CSR6_TTM_MASK     0x00400000UL
#define CSR6_TTM_SHIFT    22

/*------------------------------------------------------------------------------
 * CSR6_SF:
 *   SF field of register CSR6.
 *------------------------------------------------------------------------------
 * Store and forward
 */
#define CSR6_SF_OFFSET   0x30
#define CSR6_SF_MASK     0x00200000UL
#define CSR6_SF_SHIFT    21

/*------------------------------------------------------------------------------
 * CSR6_TR:
 *   TR field of register CSR6.
 *------------------------------------------------------------------------------
 * Threshold control bits
 */
#define CSR6_TR_OFFSET   0x30
#define CSR6_TR_MASK     0x0000C000UL
#define CSR6_TR_SHIFT    14

/*------------------------------------------------------------------------------
 * CSR6_ST:
 *   ST field of register CSR6.
 *------------------------------------------------------------------------------
 * Start/stop transmit command
 */
#define CSR6_ST_OFFSET   0x30
#define CSR6_ST_MASK     0x00002000UL
#define CSR6_ST_SHIFT    13

/*------------------------------------------------------------------------------
 * CSR6_FD:
 *   FD field of register CSR6.
 *------------------------------------------------------------------------------
 * Full-duplex mode
 */
#define CSR6_FD_OFFSET   0x30
#define CSR6_FD_MASK     0x00000200UL
#define CSR6_FD_SHIFT    9

/*------------------------------------------------------------------------------
 * CSR6_PM:
 *   PM field of register CSR6.
 *------------------------------------------------------------------------------
 * Pass all multicast
 */
#define CSR6_PM_OFFSET   0x30
#define CSR6_PM_MASK     0x00000080UL
#define CSR6_PM_SHIFT    7

/*------------------------------------------------------------------------------
 * CSR6_PR:
 *   PR field of register CSR6.
 *------------------------------------------------------------------------------
 * Promiscuous mode
 */
#define CSR6_PR_OFFSET   0x30
#define CSR6_PR_MASK     0x00000040UL
#define CSR6_PR_SHIFT    6

/*------------------------------------------------------------------------------
 * CSR6_IF:
 *   IF field of register CSR6.
 *------------------------------------------------------------------------------
 * Inverse filtering
 */
#define CSR6_IF_OFFSET   0x30
#define CSR6_IF_MASK     0x00000010UL
#define CSR6_IF_SHIFT    4

/*------------------------------------------------------------------------------
 * CSR6_PB:
 *   PB field of register CSR6.
 *------------------------------------------------------------------------------
 * Pass bad frames
 */
#define CSR6_PB_OFFSET   0x30
#define CSR6_PB_MASK     0x00000008UL
#define CSR6_PB_SHIFT    3

/*------------------------------------------------------------------------------
 * CSR6_HO:
 *   HO field of register CSR6.
 *------------------------------------------------------------------------------
 * Hash-only filtering mode
 */
#define CSR6_HO_OFFSET   0x30
#define CSR6_HO_MASK     0x00000004UL
#define CSR6_HO_SHIFT    2

/*------------------------------------------------------------------------------
 * CSR6_SR:
 *   SR field of register CSR6.
 *------------------------------------------------------------------------------
 * Start/stop receive command
 */
#define CSR6_SR_OFFSET   0x30
#define CSR6_SR_MASK     0x00000002UL
#define CSR6_SR_SHIFT    1

/*------------------------------------------------------------------------------
 * CSR6_HP:
 *   HP field of register CSR6.
 *------------------------------------------------------------------------------
 * Hash/perfect receive filtering mode
 */
#define CSR6_HP_OFFSET   0x30
#define CSR6_HP_MASK     0x00000001UL
#define CSR6_HP_SHIFT    0

/*******************************************************************************
 * CSR7 register:
 *------------------------------------------------------------------------------
 * CSR7 - Interrupt Enable Register
 */
#define CSR7_REG_OFFSET	0x38

/*------------------------------------------------------------------------------
 * CSR7_NIE:
 *   NIE field of register CSR7.
 *------------------------------------------------------------------------------
 * Normal interrupt summary enable
 */
#define CSR7_NIE_OFFSET   0x38
#define CSR7_NIE_MASK     0x00010000UL
#define CSR7_NIE_SHIFT    16

/*------------------------------------------------------------------------------
 * CSR7_AIE:
 *   AIE field of register CSR7.
 *------------------------------------------------------------------------------
 * Abnormal interrupt summary enable
 */
#define CSR7_AIE_OFFSET   0x38
#define CSR7_AIE_MASK     0x00008000UL
#define CSR7_AIE_SHIFT    15

/*------------------------------------------------------------------------------
 * CSR7_ERE:
 *   ERE field of register CSR7.
 *------------------------------------------------------------------------------
 * Early receive interrupt enable
 */
#define CSR7_ERE_OFFSET   0x38
#define CSR7_ERE_MASK     0x00004000UL
#define CSR7_ERE_SHIFT    14

/*------------------------------------------------------------------------------
 * CSR7_GTE:
 *   GTE field of register CSR7.
 *------------------------------------------------------------------------------
 * General-purpose timer overflow enable
 */
#define CSR7_GTE_OFFSET   0x38
#define CSR7_GTE_MASK     0x00000800UL
#define CSR7_GTE_SHIFT    11

/*------------------------------------------------------------------------------
 * CSR7_ETE:
 *   ETE field of register CSR7.
 *------------------------------------------------------------------------------
 * Early transmit interrupt enable
 */
#define CSR7_ETE_OFFSET   0x38
#define CSR7_ETE_MASK     0x00000400UL
#define CSR7_ETE_SHIFT    10

/*------------------------------------------------------------------------------
 * CSR7_RSE:
 *   RSE field of register CSR7.
 *------------------------------------------------------------------------------
 * Receive stopped enable
 */
#define CSR7_RSE_OFFSET   0x38
#define CSR7_RSE_MASK     0x00000100UL
#define CSR7_RSE_SHIFT    8

/*------------------------------------------------------------------------------
 * CSR7_RUE:
 *   RUE field of register CSR7.
 *------------------------------------------------------------------------------
 * Receive buffer unavailable enable
 */
#define CSR7_RUE_OFFSET   0x38
#define CSR7_RUE_MASK     0x00000080UL
#define CSR7_RUE_SHIFT    7

/*------------------------------------------------------------------------------
 * CSR7_RIE:
 *   RIE field of register CSR7.
 *------------------------------------------------------------------------------
 * Receive interrupt enable
 */
#define CSR7_RIE_OFFSET   0x38
#define CSR7_RIE_MASK     0x00000040UL
#define CSR7_RIE_SHIFT    6

/*------------------------------------------------------------------------------
 * CSR7_UNE:
 *   UNE field of register CSR7.
 *------------------------------------------------------------------------------
 * Underflow interrupt enable
 */
#define CSR7_UNE_OFFSET   0x38
#define CSR7_UNE_MASK     0x00000020UL
#define CSR7_UNE_SHIFT    5

/*------------------------------------------------------------------------------
 * CSR7_TUE:
 *   TUE field of register CSR7.
 *------------------------------------------------------------------------------
 * Transmit buffer unavailable enable
 */
#define CSR7_TUE_OFFSET   0x38
#define CSR7_TUE_MASK     0x00000004UL
#define CSR7_TUE_SHIFT    2

/*------------------------------------------------------------------------------
 * CSR7_TSE:
 *   TSE field of register CSR7.
 *------------------------------------------------------------------------------
 * Transmit stopped enable
 */
#define CSR7_TSE_OFFSET   0x38
#define CSR7_TSE_MASK     0x00000002UL
#define CSR7_TSE_SHIFT    1

/*------------------------------------------------------------------------------
 * CSR7_TIE:
 *   TIE field of register CSR7.
 *------------------------------------------------------------------------------
 * Transmit interrupt enable
 */
#define CSR7_TIE_OFFSET   0x38
#define CSR7_TIE_MASK     0x00000001UL
#define CSR7_TIE_SHIFT    0

/*******************************************************************************
 * CSR8 register:
 *------------------------------------------------------------------------------
 * CSR8 - Missed Frames and Overflow Counter Register
 */
#define CSR8_REG_OFFSET	0x40

/*------------------------------------------------------------------------------
 * CSR8_OCO:
 *   OCO field of register CSR8.
 *------------------------------------------------------------------------------
 * Overflow counter overflow
 */
#define CSR8_OCO_OFFSET   0x40
#define CSR8_OCO_MASK     0x10000000UL
#define CSR8_OCO_SHIFT    28

/*------------------------------------------------------------------------------
 * CSR8_FOC:
 *   FOC field of register CSR8.
 *------------------------------------------------------------------------------
 * FIFO overflow counter
 */
#define CSR8_FOC_OFFSET   0x40
#define CSR8_FOC_MASK     0x0FFE0000UL
#define CSR8_FOC_SHIFT    17

/*------------------------------------------------------------------------------
 * CSR8_MFO:
 *   MFO field of register CSR8.
 *------------------------------------------------------------------------------
 * Missed frame overflow
 */
#define CSR8_MFO_OFFSET   0x40
#define CSR8_MFO_MASK     0x00010000UL
#define CSR8_MFO_SHIFT    16

/*------------------------------------------------------------------------------
 * CSR8_MFC:
 *   MFC field of register CSR8.
 *------------------------------------------------------------------------------
 * Missed frame counter
 */
#define CSR8_MFC_OFFSET   0x40
#define CSR8_MFC_MASK     0x0000FFFFUL
#define CSR8_MFC_SHIFT    0

/*******************************************************************************
 * CSR9 register:
 *------------------------------------------------------------------------------
 * CSR9 - MII Management and Serial ROM Interface Register
 */
#define CSR9_REG_OFFSET	0x48

/*------------------------------------------------------------------------------
 * CSR9_MDI:
 *   MDI field of register CSR9.
 *------------------------------------------------------------------------------
 * MII management data in signal
 */
#define CSR9_MDI_OFFSET   0x48
#define CSR9_MDI_MASK     0x00080000UL
#define CSR9_MDI_SHIFT    19

/*------------------------------------------------------------------------------
 * CSR9_MII:
 *   MII field of register CSR9.
 *------------------------------------------------------------------------------
 * MII management operation mode
 */
#define CSR9_MII_OFFSET   0x48
#define CSR9_MII_MASK     0x00040000UL
#define CSR9_MII_SHIFT    18

/*------------------------------------------------------------------------------
 * CSR9_MDO:
 *   MDO field of register CSR9.
 *------------------------------------------------------------------------------
 * MII management write data
 */
#define CSR9_MDO_OFFSET   0x48
#define CSR9_MDO_MASK     0x00020000UL
#define CSR9_MDO_SHIFT    17

/*------------------------------------------------------------------------------
 * CSR9_MDC:
 *   MDC field of register CSR9.
 *------------------------------------------------------------------------------
 * MII management clock
 */
#define CSR9_MDC_OFFSET   0x48
#define CSR9_MDC_MASK     0x00010000UL
#define CSR9_MDC_SHIFT    16

/*------------------------------------------------------------------------------
 * CSR9_SDO:
 *   SDO field of register CSR9.
 *------------------------------------------------------------------------------
 * Serial ROM data output
 */
#define CSR9_SDO_OFFSET   0x48
#define CSR9_SDO_MASK     0x00000008UL
#define CSR9_SDO_SHIFT    3

/*------------------------------------------------------------------------------
 * CSR9_SDI:
 *   SDI field of register CSR9.
 *------------------------------------------------------------------------------
 * Serial ROM data input
 */
#define CSR9_SDI_OFFSET   0x48
#define CSR9_SDI_MASK     0x00000004UL
#define CSR9_SDI_SHIFT    2

/*------------------------------------------------------------------------------
 * CSR9_SCLK:
 *   SCLK field of register CSR9.
 *------------------------------------------------------------------------------
 * Serial ROM clock
 */
#define CSR9_SCLK_OFFSET   0x48
#define CSR9_SCLK_MASK     0x00000002UL
#define CSR9_SCLK_SHIFT    1

/*------------------------------------------------------------------------------
 * CSR9_SCS:
 *   SCS field of register CSR9.
 *------------------------------------------------------------------------------
 * Serial ROM chip select
 */
#define CSR9_SCS_OFFSET   0x48
#define CSR9_SCS_MASK     0x00000001UL
#define CSR9_SCS_SHIFT    0

/*******************************************************************************
 * CSR11 register:
 *------------------------------------------------------------------------------
 * CSR11 - General-Purpose Timer and Interrupt Mitigation Control Register
 */
#define CSR11_REG_OFFSET	0x58

/*------------------------------------------------------------------------------
 * CSR11_CS:
 *   CS field of register CSR11.
 *------------------------------------------------------------------------------
 * Cycle size
 */
#define CSR11_CS_OFFSET   0x58
#define CSR11_CS_MASK     0x80000000UL
#define CSR11_CS_SHIFT    31

/*------------------------------------------------------------------------------
 * CSR11_TT:
 *   TT field of register CSR11.
 *------------------------------------------------------------------------------
 * Transmit timer
 */
#define CSR11_TT_OFFSET   0x58
#define CSR11_TT_MASK     0x78000000UL
#define CSR11_TT_SHIFT    27

/*------------------------------------------------------------------------------
 * CSR11_NTP:
 *   NTP field of register CSR11.
 *------------------------------------------------------------------------------
 * Number of transmit packets
 */
#define CSR11_NTP_OFFSET   0x58
#define CSR11_NTP_MASK     0x07000000UL
#define CSR11_NTP_SHIFT    24

/*------------------------------------------------------------------------------
 * CSR11_RT:
 *   RT field of register CSR11.
 *------------------------------------------------------------------------------
 * Receive timer
 */
#define CSR11_RT_OFFSET   0x58
#define CSR11_RT_MASK     0x00F00000UL
#define CSR11_RT_SHIFT    20

/*------------------------------------------------------------------------------
 * CSR11_NRP:
 *   NRP field of register CSR11.
 *------------------------------------------------------------------------------
 * Number of receive packets
 */
#define CSR11_NRP_OFFSET   0x58
#define CSR11_NRP_MASK     0x000E0000UL
#define CSR11_NRP_SHIFT    17

/*------------------------------------------------------------------------------
 * CSR11_CON:
 *   CON field of register CSR11.
 *------------------------------------------------------------------------------
 * Continuous mode
 */
#define CSR11_CON_OFFSET   0x58
#define CSR11_CON_MASK     0x00010000UL
#define CSR11_CON_SHIFT    16

/*------------------------------------------------------------------------------
 * CSR11_TIM:
 *   TIM field of register CSR11.
 *------------------------------------------------------------------------------
 * Timer value
 */
#define CSR11_TIM_OFFSET   0x58
#define CSR11_TIM_MASK     0x0000FFFFUL
#define CSR11_TIM_SHIFT    0

#ifdef __cplusplus
}
#endif

#endif /* MSS_ETHERNET_MAC_REGISTERS_H_*/
