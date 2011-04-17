/***************************************************************************//**
 * @file
 * SmartFusion MSS Ethernet MAC header file.
 *
 * (c) Copyright 2007 Actel Corporation
 *
 * SVN $Revision: 2364 $
 * SVN $Date: 2010-03-01 17:58:41 +0000 (Mon, 01 Mar 2010) $
 *
 *******************************************************************************/

#ifndef __MSS_ETHERNET_MAC_H
#define __MSS_ETHERNET_MAC_H	1

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif 

/******************************** DEFINES *************************************/

/*******************************************************************************
 * Configure values.
 */
/**
 * Receive all.
 * When set, all incoming frames are received, regardless of their destination address.
 * An address check is performed, and the result of the check is written into the receive
 * descriptor.
 */
#define MSS_MAC_CFG_RECEIVE_ALL                         0x00000001u

/**
 * Transmit threshold mode.
 * 1 - Transmit FIFO threshold set for 100 Mbps mode
 * 0 - Transmit FIFO threshold set for 10 Mbps mode
 * This bit can be changed only when a transmit process is in a stopped state.
 */
#define MSS_MAC_CFG_TRANSMIT_THRESHOLD_MODE             0x00000002u

/**
 * Store and forward.
 * When set, the transmission starts after a full packet is written into the transmit
 * FIFO, regardless of the current FIFO threshold level.
 * This bit can be changed only when the transmit process is in the stopped state.
 */
#define MSS_MAC_CFG_STORE_AND_FORWARD                   0x00000004u

/**
 * Threshold control bits.
 * These bits, together with TTM, SF, and PS, control the threshold level for the
 * transmit FIFO.
 */
#define MSS_MAC_CFG_THRESHOLD_CONTROL_00                0x00000000u
#define MSS_MAC_CFG_THRESHOLD_CONTROL_01                0x00000008u
#define MSS_MAC_CFG_THRESHOLD_CONTROL_10                0x00000010u
#define MSS_MAC_CFG_THRESHOLD_CONTROL_11                0x00000018u

/**
 * Full-duplex mode.
 * 0 - Half-duplex mode <br>
 * 1 - Forcing full-duplex mode <br>
 * Changing of this bit is allowed only when both the transmitter and receiver processes
 * are in the stopped state.
 */
#define MSS_MAC_CFG_FULL_DUPLEX_MODE                    0x00000020u

/**
 * Pass all multicast.
 * When set, all frames with multicast destination addresses will be received, regardless
 * of the address check result.
 */
#define MSS_MAC_CFG_PASS_ALL_MULTICAST                  0x00000040u

/**
 * Promiscuous mode.
 * When set, all frames will be received regardless of the address check result. An
 * address check is not performed.
 */
#define MSS_MAC_CFG_PROMISCUOUS_MODE                    0x00000080u

/**
 * Inverse filtering (read-only).
 * If this bit is set when working in a perfect filtering mode, the receiver performs an
 * inverse filtering during the address check process.
 * The 'filtering type' bits of the setup frame determine the state of this bit.
 */
#define MSS_MAC_CFG_INVERSE_FILTERING                   0x00000100u

/**
 * Pass bad frames.
 * When set, Core10/100 transfers all frames into the data buffers, regardless of the
 * receive errors. This allows the runt frames, collided fragments, and truncated frames
 * to be received.
 */
#define MSS_MAC_CFG_PASS_BAD_FRAMES                     0x00000200u

/**
 * Hash-only filtering mode (read-only).
 * When set, Core10/100 performs an imperfect filtering over both the multicast and
 * physical addresses.
 * The 'filtering type' bits of the setup frame determine the state of this bit.
 */
#define MSS_MAC_CFG_HASH_ONLY_FILTERING_MODE            0x00000400u

/**
 * Hash/perfect receive filtering mode (read-only).
 * 0 - Perfect filtering of the incoming frames is performed according to the physical
 * addresses specified in a setup frame. <br>
 * 1 - Imperfect filtering over the frames with the multicast addresses is performed
 * according to the hash table specified in a setup frame. <br>
 * A physical address check is performed according to the CSR6.2 (HO, hash-only) bit.
 * When both the HO and HP bits are set, an imperfect filtering is performed on all of
 * the addresses.
 * The 'filtering type' bits of the setup frame determine the state of this bit.
 */
#define MSS_MAC_CFG_HASH_PERFECT_RECEIVE_FILTERING_MODE 0x00000800u


/*******************************************************************************
 * Link status values.
 */
#define MSS_MAC_LINK_STATUS_LINK  0x0001u   /**< Link up/down */
#define MSS_MAC_LINK_STATUS_100MB 0x0002u   /**< Connection is 100Mb/10Mb */
#define MSS_MAC_LINK_STATUS_FDX   0x0004u   /**< Connection is full/half duplex */


/**
 * Size of the max packet that can be received/transmited.
 */
#define MSS_MAX_PACKET_SIZE  1514uL

/**
 * Size of a receive/transmit buffer.
 * Buffer size must be enough big to hold a full frame and must be multiple of
 * four. For rx buffer +4 bytes allocated for crc values. These bytes doesn't
 * copied to the user buffer.
 */
#define MSS_TX_BUFF_SIZE  ((MSS_MAX_PACKET_SIZE + 3u) & (~(uint32_t)3))
#define MSS_RX_BUFF_SIZE  ((MSS_MAX_PACKET_SIZE + 7u) & (~(uint32_t)3))

/*******************************************************************************
 * Time out values.
 */
#define MSS_MAC_NONBLOCKING		0u
#define MSS_MAC_BLOCKING		0xFFFFFFFFUL

/***************************************************************************//**
 * MAC events.
 */
#define MSS_MAC_EVENT_PACKET_SEND		1u
#define MSS_MAC_EVENT_PACKET_RECEIVED	2u

/***************************************************************************//**
 * PHY addresses.
 */
#define MSS_PHY_ADDRESS_MIN				0u
#define MSS_PHY_ADDRESS_MAX				31u
#define MSS_PHY_ADDRESS_AUTO_DETECT		255u

/***************************************************************************//**
 * Listener function type defines the function prototype that might be followed 
 * by MAC_isr which is triggered with each receive and transmit related interrupts.
 * Listener functions should follow the following prototype:
 *		void MAC_Listener( uint32_t events );
 * The parameter is used to inform the listener function about the triggering event
 * or events. Events input to the system are:
 *      #define MSS_MAC_EVENT_PACKET_SEND		1
 *      #define MSS_MAC_EVENT_PACKET_RECEIVED	2
 * Listener function should be defined by the application using this driver if 
 * needed. This function may be assigned to the driver using MAC_set_callback
 * routine and may be un assigned again by using the same routine with a NULL pointer
 * as the event listener function. It is recommended to use this property for interrupt
 * triggered systems and it is not recommended for polling mechanisms.
 */
typedef void (*MSS_MAC_callback_t)(uint32_t events);

/***************************************************************************//**
 * Statistics counter identifiers are used with MAC_get_statistics routine to 
 * receive the count of the requested errors/interrupts occurrences.
 *
 * MSS_MAC_RX_INTERRUPTS
 *      Used to receive the number of receive interrupts occurred.
 *
 * MSS_MAC_RX_FILTERING_FAIL
 *      Used to receive the number of received frames which did not pass the
 *      address recognition process.
 *
 * MSS_MAC_RX_DESCRIPTOR_ERROR
 *      Used to receive the number of occurrences of; no receive buffer was
 *      available when trying to store the received data.
 *
 * MSS_MAC_RX_RUNT_FRAME
 *      Used to receive the number of occurrences of; the frame is damaged by a
 *      collision or by a premature termination before the end of a collision
 *      window.
 *
 * MSS_MAC_RX_NOT_FIRST
 *      Used to receive the number of occurrences of; start of the frame is not
 *      the first descriptor of a frame.
 *
 * MSS_MAC_RX_NOT_LAST
 *      Used to receive the number of occurrences of; end of the frame is not
 *      the first descriptor of a frame.
 *
 * MSS_MAC_RX_FRAME_TOO_LONG
 *      Used to receive the number of occurrences of; a current frame is longer
 *      than maximum size of 1,518 bytes, as specified by 802.3.
 *
 * MSS_MAC_RX_COLLISION_SEEN
 *      Used to receive the number of occurrences of; a late collision was seen
 *      (collision after 64 bytes following SFD).
 *
 * MSS_MAC_RX_CRC_ERROR
 *      Used to receive the number of occurrences of; a CRC error has occurred
 *      in the received frame.
 *
 * MSS_MAC_RX_FIFO_OVERFLOW
 *      Used to receive the number of frames not accepted due to the receive
 *      FIFO overflow.
 *
 * MSS_MAC_RX_MISSED_FRAME
 *      Used to receive the number of frames not accepted due to the
 *      unavailability of the receive descriptor.
 *
 * MSS_MAC_TX_INTERRUPTS
 *      Used to receive the number of transmit interrupts occurred.
 *
 * MSS_MAC_TX_LOSS_OF_CARRIER
 *      Used to receive the number of occurrences of; a loss of the carrier
 *      during a transmission.
 *
 * MSS_MAC_TX_NO_CARRIER
 *      Used to receive the number of occurrences of; the carrier was not asserted
 *      by an external transceiver during the transmission.
 *
 * MSS_MAC_TX_LATE_COLLISION
 *      Used to receive the number of occurrences of; a collision was detected
 *      after transmitting 64 bytes.
 *
 * MSS_MAC_TX_EXCESSIVE_COLLISION
 *      Used to receive the number of occurrences of; the transmission was aborted
 *      after 16 retries.
 *
 * MSS_MAC_TX_COLLISION_COUNT
 *      Used to receive the number of collisions occurred.
 *
 * MSS_MAC_TX_UNDERFLOW_ERROR
 *      Used to receive the number of occurrences of; the FIFO was empty during
 *      the frame transmission.
 */
typedef enum {
	MSS_MAC_RX_INTERRUPTS,
	MSS_MAC_RX_FILTERING_FAIL,
	MSS_MAC_RX_DESCRIPTOR_ERROR,
	MSS_MAC_RX_RUNT_FRAME,
	MSS_MAC_RX_NOT_FIRST,
	MSS_MAC_RX_NOT_LAST,
	MSS_MAC_RX_FRAME_TOO_LONG,
	MSS_MAC_RX_COLLISION_SEEN,
	MSS_MAC_RX_CRC_ERROR,
	MSS_MAC_RX_FIFO_OVERFLOW,
	MSS_MAC_RX_MISSED_FRAME,
	
	MSS_MAC_TX_INTERRUPTS,
	MSS_MAC_TX_LOSS_OF_CARRIER,
	MSS_MAC_TX_NO_CARRIER,
	MSS_MAC_TX_LATE_COLLISION,
	MSS_MAC_TX_EXCESSIVE_COLLISION,
	MSS_MAC_TX_COLLISION_COUNT,
	MSS_MAC_TX_UNDERFLOW_ERROR
} mss_mac_statistics_id_t; 

/******************************* FUNCTIONS ************************************/

/***************************************************************************//**
 * Initializes an Ethernet MAC controller and data structures.
 * This function will prepare the Ethernet Controller for first time use in a
 * given hardware/software configuration. This function should be called before
 * any other Ethernet API functions are called.
 *
 * Initialization of registers - config registers, enable Tx/Rx interrupts,
 * enable Tx/Rx, initialize MAC addr, init PHY, autonegotiation, MAC address
 * filter table (unicast/multicast)/hash init
 *
 */
void
MSS_MAC_init
(
    uint8_t phy_address
);


/***************************************************************************//**
 * Sets the configuration of the Ethernet Controller.
 * After the MAC_init function has been called, this API function can be
 * used to configure the various features of the Ethernet Controller.
 *
 * @param configuration The logical OR of the following values:
 *    - #MSS_MAC_CFG_RECEIVE_ALL
 *    - #MSS_MAC_CFG_TRANSMIT_THRESHOLD_MODE
 *    - #MSS_MAC_CFG_STORE_AND_FORWARD
 *    - #MSS_MAC_CFG_THRESHOLD_CONTROL_[00,01,10,11]
 *    - #MSS_MAC_CFG_FULL_DUPLEX_MODE
 *    - #MSS_MAC_CFG_PASS_ALL_MULTICAST
 *    - #MSS_MAC_CFG_PROMISCUOUS_MODE
 *    - #MSS_MAC_CFG_PASS_BAD_FRAMES
 * @see   MAC_get_configuration()
 */
void
MSS_MAC_configure
(
    uint32_t configuration
);


/***************************************************************************//**
 * Returns the configuration of the Ethernet Controller.
 * After the MAC_init function has been called, this API function can be used to 
 * get the configuration of the Ethernet Controller.
 *
 * @return              The logical OR of the following values:
 *    - #MSS_MAC_CFG_RECEIVE_ALL
 *    - #MSS_MAC_CFG_TRANSMIT_THRESHOLD_MODE
 *    - #MSS_MAC_CFG_STORE_AND_FORWARD
 *    - #MSS_MAC_CFG_THRESHOLD_CONTROL_[00,01,10,11]
 *    - #MSS_MAC_CFG_FULL_DUPLEX_MODE
 *    - #MSS_MAC_CFG_PASS_ALL_MULTICAST
 *    - #MSS_MAC_CFG_PROMISCUOUS_MODE
 *    - #MSS_MAC_CFG_INVERSE_FILTERING
 *    - #MSS_MAC_CFG_PASS_BAD_FRAMES
 *    - #MSS_MAC_CFG_HASH_ONLY_FILTERING_MODE
 *    - #MSS_MAC_CFG_HASH_PERFECT_RECEIVE_FILTERING_MODE
 * @see   MAC_configure()
 */
int32_t
MSS_MAC_get_configuration
(
    void
);


/***************************************************************************//**
 * Sends a packet to the Ethernet Controller.
 * This function writes pacLen bytes of the packet contained in pacData into the
 * transmit FIFO of the controller and then activates the transmitter for this
 * packet. If space is available in FIFO, the function will return once lBufLen
 * bytes of the packet have been placed into the FIFO and the transmitter has been
 * started. The function will not wait for the transmission to complete. If space
 * is not available in FIFO, the function will keep trying till time_out expires,
 * if MSS_MAC_BLOCKING value is given as time_out, function will wait for the
 * transmission to complete.
 *
 * @param pacData       the pointer to the packet data to be transmitted.
 * @param pacLen        number of bytes in the packet to be transmitted.
 * @param time_out      Time out value for transmision.
 * 					    If value is #MSS_MAC_BLOCKING, there will be no time out.
 * 		    			If value is #MSS_MAC_NONBLOCKING, function will return immediately 
 * 		    			on buffer full case.
 * 		    			Otherwise value must be greater than 0 and smaller than 
 * 		    			0x01000000.
 * @return				Returns 0 if time out occurs otherwise returns size 
 * 						of the packet.
 * @see   MAC_rx_packet()
 */
int32_t
MSS_MAC_tx_packet
(
    const uint8_t *pacData,
    uint16_t pacLen,
    uint32_t time_out
);


/***************************************************************************//**
 * Returns available packet's size.
 *
 * @return              Size of packet, bigger than 0, if a packet is available,
 *                      if not, returns 0. 
 * @see   MAC_rx_packet()
 */
int32_t
MSS_MAC_rx_pckt_size
(
    void
);



/***************************************************************************//**
 * Prepares the RX descriptor for receiving packets.
 *
 * @return              void
 * @see   MAC_rx_packet()
 */
void
MSS_MAC_prepare_rx_descriptor
(
    void
);

/***************************************************************************//**
 * Receives a packet from the Ethernet Controller.
 * This function reads a packet from the receive FIFO of the controller and
 * places it into pacData. If time_out parameter is zero the function will return 
 * immediately (after the copy operation if data is available. Otherwise the function
 * will keep trying to read till time_out expires or data is read, if MSS_MAC_BLOCKING 
 * value is given as time_out, function will wait for the reception to complete.
 *
 * @param pacData       The pointer to the buffer where received packet data will
 *                      be copied. Memory for the buffer should be allocated prior 
 *                      to calling this function.
 * @param pacLen        Size of the buffer, which the received data will be copied in,
 *                      given in number of bytes.
 * @param time_out      Time out value in milli seconds for receiving.
 * 					    if value is #MSS_MAC_BLOCKING, there will be no time out.
 * 					    if value is #MSS_MAC_NONBLOCKING, function will return immediately
 * 					    if there is no packet waiting.
 * 					    Otherwise value must be greater than 0 and smaller than 
 * 					    0x01000000.
 * @return              Size of packet if packet fits in pacData.
 * 					    0 if there is no received packet.
 * @see   MAC_rx_pckt_size()
 * @see   MAC_tx_packet()
 */
int32_t
MSS_MAC_rx_packet
(
    uint8_t **pacData,
    uint16_t pacLen,
    uint32_t time_out
);


/***************************************************************************//**
  Receives a packet from the Ethernet Controller.
  The MSS_MAC_rx_packet_ptrset() function is very similar to the MSS_MAC_rx_packet()
  function, in that it receives data from the MSS Ethernet MAC. The difference
  is that it sets pacData to point to the memory buffer where the MSS Ethernet
  MAC copied the received packet instead of copying the received packet into a
  buffer provided by the application. After this function is called and data is
  used by the user application or copied to another buffer, the
  MSS_MAC_prepare_rx_descriptor() function must be called to free up the receive
  memory buffer used by the MSS Ethernet MAC
 
  @param pacData
   The pacData parameter is a pointer to a memory buffer pointer. The uint8_t
   pointer pointed to by the pacData parameter will contain the address of the
   memory buffer containing the received packet after this function returns. The
   value of pacData is only valid if the return value is larger than zero,
   indicating that a packet was received.
   
  @param time_out
    The time_out parameter is the timeout value for the transmission in milliseconds.
    The time_out parameter value can be one of the following values:
        • Unsigned integer greater than 0 and less than 0x01000000
        • MSS_MAC_BLOCKING – there will be no timeout. 
        • MSS_MAC_NONBLOCKING – the function will return immediately if no packets
          have been received. 

  @return
  	The function returns the size of the packet if the packet fits in pacData.
    Returns zero if there is no received packet.
                        
  @see   MAC_rx_pckt_size()
  @see   MAC_tx_packet()
 */
int32_t
MSS_MAC_rx_packet_ptrset
(
    uint8_t **pacData,
    uint32_t time_out
);

/***************************************************************************//**
 * Returns the status of connection by reading it from the PHY.
 *
 * @return              the logical OR of the following values:
 *      #MSS_MAC_LINK_STATUS_LINK    - Link up/down
 *      #MSS_MAC_LINK_STATUS_100MB   - Connection is 100Mb/10Mb
 *      #MSS_MAC_LINK_STATUS_FDX     - Connection is full/half duplex
 * @see   MAC_auto_setup_link()
 */
int32_t
MSS_MAC_link_status
(
    void
);


/***************************************************************************//**
 * Setups the link between PHY and MAC and returns the status of connection.
 *
 * @return              the logical OR of the following values:
 *      #MSS_MAC_LINK_STATUS_LINK    - Link up/down
 *      #MSS_MAC_LINK_STATUS_100MB   - Connection is 100Mb/10Mb
 *      #MSS_MAC_LINK_STATUS_FDX     - Connection is full/half duplex
 * @see   MAC_link_status()
 */
int32_t
MSS_MAC_auto_setup_link
(
    void
);


/***************************************************************************//**
 * Sets mac address.
 *
 * @param new_address   Pointer to then new address value (6 bytes of data)
 * @see   MAC_get_mac_address()
 */
void
MSS_MAC_set_mac_address
(
    const uint8_t *new_address
);


/***************************************************************************//**
 * Returns mac address.
 *
 * @param address       Pointer to the parameter to receive the MAC address.
 * @see   MAC_set_mac_address()
 */
void
MSS_MAC_get_mac_address
(
    uint8_t *address
);


/***************************************************************************//**
 * Sets mac address filters.
 * If less than 15 addresses are subscribed, system works on perfect filtering mode
 * else system works in hash table mode
 *
 * @param filter_count  number of addresses
 * @param filters       Pointer to addresses to be filtered
 */
void
MSS_MAC_set_mac_filters
(
    uint16_t filter_count,
	const uint8_t *filters
);

/***************************************************************************//**
 * Sets MAC event listener.
 * Sets the given event listener function to be triggered inside MAC_isr().
 * Assigning NULL pointer as the listener function will disable it.
 *
 * @param listener      function pointer to a MSS_MAC_callback_t function
 * @see   MAC_isr()
 */
void
MSS_MAC_set_callback
(
    MSS_MAC_callback_t listener
);


/***************************************************************************//**
 * Returns description of latest error happened.
 *
 * @return              A string describing the error. This string must not be 
 * 						modified by the application.
 */
const int8_t* 
MSS_MAC_last_error
(
    void
);


/***************************************************************************//**
 * Returns statistics counter of stat_id identifier.
 * 
 * @param stat_id		Identifier of statistics counter.
 * @return				Statistics counter of stat_id identifier.
 * 						On error returns 0.
 */
uint32_t
MSS_MAC_get_statistics
(
	mss_mac_statistics_id_t stat_id
);

#ifdef __cplusplus
}
#endif

#endif	/* __MSS_ETHERNET_MAC_H */

