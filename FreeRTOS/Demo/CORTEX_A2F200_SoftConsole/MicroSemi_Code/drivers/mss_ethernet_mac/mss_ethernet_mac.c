/***************************************************************************//**
 * @file
 * SmartFusion MSS Ethernet MAC driver implementation.
 *
 * (c) Copyright 2007 Actel Corporation
 *
 * SVN $Revision: 2369 $
 * SVN $Date: 2010-03-01 18:31:45 +0000 (Mon, 01 Mar 2010) $
 *
 ******************************************************************************/

/*
 *
 *
 * NOTE:  This driver has been modified specifically for use with the* uIP stack.
 * It is no longer a generic driver.
 *
 *
 */

#ifdef __cplusplus
extern "C" {
#endif

#include "FreeRTOS.h"
#include "task.h"

#include "crc32.h"

#include "mss_ethernet_mac.h"
#include "mss_ethernet_mac_regs.h"
#include "mss_ethernet_mac_desc.h"
#include "mss_ethernet_mac_conf.h"
#include "../../CMSIS/mss_assert.h"

#include "phy.h"

/**************************** INTERNAL DEFINES ********************************/

#define MAC_CHECK(CHECK,ERRNO)	\
	{if(!(CHECK)){g_mss_mac.last_error=(ERRNO); configASSERT((CHECK));}}

/*
 * Flags
 */
#define FLAG_MAC_INIT_DONE		1u
#define FLAG_PERFECT_FILTERING	2u
#define FLAG_CRC_DISABLE		4u
#define FLAG_EXCEED_LIMIT		8u

/*
 * Return types
 */
#define MAC_OK                    0
#define MAC_FAIL                  (-1)
#define MAC_WRONG_PARAMETER       (-2)
#define MAC_TOO_BIG_PACKET        (-3)
#define MAC_BUFFER_IS_FULL        (-4)
#define MAC_NOT_ENOUGH_SPACE      (-5)
#define MAC_TIME_OUT			  (-6)
#define MAC_TOO_SMALL_PACKET      (-7)

/* Allocating this many buffers will always ensure there is one free as, even
though TX_RING_SIZE is set to two, the two Tx descriptors will only ever point
to the same buffer. */
#define macNUM_BUFFERS RX_RING_SIZE + TX_RING_SIZE
#define macBUFFER_SIZE 1488

/***************************************************************/
MAC_instance_t g_mss_mac;

/**************************** INTERNAL DATA ***********************************/
#define ERROR_MESSAGE_COUNT		8
#define MAX_ERROR_MESSAGE_WIDTH 40
static const int8_t unknown_error[] = "Unknown error";
static const int8_t ErrorMessages[][MAX_ERROR_MESSAGE_WIDTH] = {
	"No error occured",
	"Method failed",
	"Wrong parameter pased to function",
	"Frame is too long",
	"Not enough space in buffer",
	"Not enough space in buffer",
	"Timed out",
	"Frame is too small"
};

/*
 * Null variables
 */
static uint8_t* 		NULL_buffer;
static MSS_MAC_callback_t 	NULL_callback;

/* Declare the uip_buf as a pointer, rather than the traditional array, as this
is a zero copy driver.  uip_buf just gets set to whichever buffer is being
processed. */
unsigned char *uip_buf = NULL;

/**************************** INTERNAL FUNCTIONS ******************************/

static int32_t	MAC_dismiss_bad_frames( void );
static int32_t	MAC_send_setup_frame( void );

static int32_t	MAC_stop_transmission( void );
static void		MAC_start_transmission( void );
static int32_t	MAC_stop_receiving( void );
static void		MAC_start_receiving( void );

static void		MAC_set_time_out( uint32_t time_out );
static uint32_t	MAC_get_time_out( void );

static void     MAC_memset(uint8_t *s, uint8_t c, uint32_t n);
static void     MAC_memcpy(uint8_t *dest, const uint8_t *src, uint32_t n);
static void     MAC_memset_All(MAC_instance_t *s, uint32_t c);

static unsigned char *MAC_obtain_buffer( void );
static void MAC_release_buffer( unsigned char *pcBufferToRelease );

#if( TX_RING_SIZE != 2 )
	#error This uIP Ethernet driver required TX_RING_SIZE to be set to 2
#endif

/* Buffers that will dynamically be allocated to/from the Tx and Rx descriptors.
The union is used for alignment only. */
static union xMAC_BUFFERS
{
	unsigned long ulAlignmentVariable; /* For alignment only, not used anywhere. */
	unsigned char ucBuffer[ macNUM_BUFFERS ][ macBUFFER_SIZE ];
} xMACBuffers;

/* Each array position indicates whether or not the buffer of the same index
is currently allocated to a descriptor (pdTRUE) or is free for use (pdFALSE). */
static unsigned char ucMACBufferInUse[ macNUM_BUFFERS ] = { 0 };

/***************************************************************************//**
 * Initializes the Ethernet Controller.
 * This function will prepare the Ethernet Controller for first time use in a
 * given hardware/software configuration. This function should be called before
 * any other Ethernet API functions are called.
 *
 * Initialization of registers - config registers, enable Tx/Rx interrupts,
 * enable Tx/Rx, initialize MAC addr, init PHY, autonegotiation, MAC address
 * filter table (unicats/multicast)/hash init
 */
void
MSS_MAC_init
(
	uint8_t phy_address
)
{
    const uint8_t mac_address[6] = { DEFAULT_MAC_ADDRESS };
    int32_t a;

	/* To start with all buffers are free. */
	for( a = 0; a < macNUM_BUFFERS; a++ )
	{
		ucMACBufferInUse[ a ] = pdFALSE;
	}
	
    /* Try to reset chip */
    MAC_BITBAND->CSR0_SWR = 1u;

    do
    {
    	vTaskDelay( 10 );
    } while ( 1u == MAC_BITBAND->CSR0_SWR );

    /* Check reset values of some registers to constrol
     * base address validity */
    configASSERT( MAC->CSR0 == 0xFE000000uL );
    configASSERT( MAC->CSR5 == 0xF0000000uL );
    configASSERT( MAC->CSR6 == 0x32000040uL );

    /* Instance setup */
    MAC_memset_All( &g_mss_mac, 0u );

    g_mss_mac.base_address = MAC_BASE;
    g_mss_mac.phy_address = phy_address;

    for( a=0; a<RX_RING_SIZE; a++ )
    {
        /* Give the ownership to the MAC */
        g_mss_mac.rx_descriptors[a].descriptor_0 = RDES0_OWN;
        g_mss_mac.rx_descriptors[a].descriptor_1 = (MSS_RX_BUFF_SIZE << RDES1_RBS1_OFFSET);
		
		/* Allocate a buffer to the descriptor, then mark the buffer as in use
		(not free). */
        g_mss_mac.rx_descriptors[a].buffer_1 = ( unsigned long ) &( xMACBuffers.ucBuffer[ a ][ 0 ] );
		ucMACBufferInUse[ a ] = pdTRUE;
    }
    g_mss_mac.rx_descriptors[RX_RING_SIZE-1].descriptor_1 |= RDES1_RER;

    for( a = 0; a < TX_RING_SIZE; a++ )
    {
		/* Buffers only get allocated to the Tx buffers when something is
		actually tranmitted. */
        g_mss_mac.tx_descriptors[a].buffer_1 = ( unsigned long ) NULL;
    }
    g_mss_mac.tx_descriptors[TX_RING_SIZE - 1].descriptor_1 |= TDES1_TER;

    /* Configurable settings */
    MAC_BITBAND->CSR0_DBO = DESCRIPTOR_BYTE_ORDERING_MODE;
    MAC->CSR0 = (MAC->CSR0 & ~CSR0_PBL_MASK) | ((uint32_t)PROGRAMMABLE_BURST_LENGTH << CSR0_PBL_SHIFT);
    MAC_BITBAND->CSR0_BLE = BUFFER_BYTE_ORDERING_MODE;
    MAC_BITBAND->CSR0_BAR = (uint32_t)BUS_ARBITRATION_SCHEME;

    /* Fixed settings */
    /* No space between descriptors */
    MAC->CSR0 = MAC->CSR0 &~ CSR0_DSL_MASK;
    /* General-purpose timer works in continuous mode */
    MAC_BITBAND->CSR11_CON = 1u;
    /* Start general-purpose */
    MAC->CSR11 =  (MAC->CSR11 & ~CSR11_TIM_MASK) | (0x0000FFFFuL << CSR11_TIM_SHIFT);

	/* Ensure promiscous mode is off (it should be by default anyway). */
	MAC_BITBAND->CSR6_PR = 0;
	
	/* Perfect filter. */
	MAC_BITBAND->CSR6_HP = 1;
	
	/* Pass multcast. */
	MAC_BITBAND->CSR6_PM = 1;
	
    /* Set descriptors */
    MAC->CSR3 = (uint32_t)&(g_mss_mac.rx_descriptors[0].descriptor_0);
    MAC->CSR4 = (uint32_t)&(g_mss_mac.tx_descriptors[0].descriptor_0);

	/* enable normal interrupts */
    MAC_BITBAND->CSR7_NIE = 1u;

    /* Set default MAC address and reset mac filters */
   	MAC_memcpy( g_mss_mac.mac_address, mac_address, 6u );
 	MSS_MAC_set_mac_address((uint8_t *)mac_address);
	
    /* Detect PHY */
    if( g_mss_mac.phy_address > MSS_PHY_ADDRESS_MAX )
    {
    	PHY_probe();
    	configASSERT( g_mss_mac.phy_address <= MSS_PHY_ADDRESS_MAX );
    }

    /* Reset PHY */
    PHY_reset();

	/* Configure chip according to PHY status */
    MSS_MAC_auto_setup_link();
	
	/* Ensure uip_buf starts by pointing somewhere. */
	uip_buf = MAC_obtain_buffer();	
}


/***************************************************************************//**
 * Sets the configuration of the Ethernet Controller.
 * After the EthernetInit function has been called, this API function can be
 * used to configure the various features of the Ethernet Controller.
 *
 * @param instance      Pointer to a MAC_instance_t structure
 * @param config        The logical OR of the following values:
 *    - #MSS_MAC_CFG_RECEIVE_ALL
 *    - #MSS_MAC_CFG_TRANSMIT_THRESHOLD_MODE
 *    - #MSS_MSS_MAC_CFG_STORE_AND_FORWARD
 *    - #MAC_CFG_THRESHOLD_CONTROL_[00,01,10,11]
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
)
{
    int32_t ret;

    ret = MAC_stop_transmission();
    configASSERT( ret == MAC_OK );

    ret = MAC_stop_receiving();
    configASSERT( ret == MAC_OK );

    MAC_BITBAND->CSR6_RA = (uint32_t)(((configuration & MSS_MAC_CFG_RECEIVE_ALL) != 0u) ? 1u : 0u );
    MAC_BITBAND->CSR6_TTM = (((configuration & MSS_MAC_CFG_TRANSMIT_THRESHOLD_MODE) != 0u) ? 1u : 0u );
    MAC_BITBAND->CSR6_SF = (uint32_t)(((configuration & MSS_MAC_CFG_STORE_AND_FORWARD) != 0u) ? 1u : 0u );

    switch( configuration & MSS_MAC_CFG_THRESHOLD_CONTROL_11 ) {
    case MSS_MAC_CFG_THRESHOLD_CONTROL_00:
        MAC->CSR6 = MAC->CSR6 & ~CSR6_TR_MASK;
        break;
    case MSS_MAC_CFG_THRESHOLD_CONTROL_01:
        MAC->CSR6 = (MAC->CSR6 & ~CSR6_TR_MASK) | ((uint32_t)1 << CSR6_TR_SHIFT );
        break;
    case MSS_MAC_CFG_THRESHOLD_CONTROL_10:
        MAC->CSR6 = (MAC->CSR6 & ~CSR6_TR_MASK) | ((uint32_t)2 << CSR6_TR_SHIFT );
        break;
    case MSS_MAC_CFG_THRESHOLD_CONTROL_11:
        MAC->CSR6 = (MAC->CSR6 & ~CSR6_TR_MASK) | ((uint32_t)3 << CSR6_TR_SHIFT );
        break;
    default:
        break;
    }
    MAC_BITBAND->CSR6_FD = (uint32_t)(((configuration & MSS_MAC_CFG_FULL_DUPLEX_MODE) != 0u) ? 1u : 0u );
    MAC_BITBAND->CSR6_PM = (uint32_t)(((configuration & MSS_MAC_CFG_PASS_ALL_MULTICAST) != 0u) ? 1u : 0u );
    MAC_BITBAND->CSR6_PR = (uint32_t)(((configuration & MSS_MAC_CFG_PROMISCUOUS_MODE) != 0u) ? 1u : 0u );
    MAC_BITBAND->CSR6_PB = (uint32_t)(((configuration & MSS_MAC_CFG_PASS_BAD_FRAMES) != 0u) ? 1u : 0u );
    PHY_set_link_type( (uint8_t)
        ((((configuration & MSS_MAC_CFG_TRANSMIT_THRESHOLD_MODE) != 0u) ? MSS_MAC_LINK_STATUS_100MB : 0u ) |
        (((configuration & MSS_MAC_CFG_FULL_DUPLEX_MODE) != 0u) ? MSS_MAC_LINK_STATUS_FDX : 0u )) );

    MSS_MAC_auto_setup_link();
}


/***************************************************************************//**
 * Returns the configuration of the Ethernet Controller.
 *
 * @param instance      Pointer to a MAC_instance_t structure
 * @return              The logical OR of the following values:
 *    - #MSS_MAC_CFG_RECEIVE_ALL
 *    - #MSS_MAC_CFG_TRANSMIT_THRESHOLD_MODE
 *    - #MSS_MAC_CFG_STORE_AND_FORWARD
 *    - #MAC_CFG_THRESHOLD_CONTROL_[00,01,10,11]
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
MSS_MAC_get_configuration( void )
{
    uint32_t configuration;

    configuration = 0u;
    if( MAC_BITBAND->CSR6_RA != 0u ) {
        configuration |= MSS_MAC_CFG_RECEIVE_ALL;
    }

    if( MAC_BITBAND->CSR6_TTM != 0u ) {
        configuration |= MSS_MAC_CFG_TRANSMIT_THRESHOLD_MODE;
    }

    if( MAC_BITBAND->CSR6_SF != 0u ) {
        configuration |= MSS_MAC_CFG_STORE_AND_FORWARD;
    }

    switch( (MAC->CSR6 & CSR6_TR_MASK) >> CSR6_TR_SHIFT ) {
    case 1: configuration |= MSS_MAC_CFG_THRESHOLD_CONTROL_01; break;
    case 2: configuration |= MSS_MAC_CFG_THRESHOLD_CONTROL_10; break;
    case 3: configuration |= MSS_MAC_CFG_THRESHOLD_CONTROL_11; break;
    default: break;
    }
    if( MAC_BITBAND->CSR6_FD != 0u ) {
        configuration |= MSS_MAC_CFG_FULL_DUPLEX_MODE;
    }

    if( MAC_BITBAND->CSR6_PM != 0u ) {
        configuration |= MSS_MAC_CFG_PASS_ALL_MULTICAST;
    }

    if( MAC_BITBAND->CSR6_PR != 0u ) {
        configuration |= MSS_MAC_CFG_PROMISCUOUS_MODE;
    }

    if( MAC_BITBAND->CSR6_IF != 0u ) {
        configuration |= MSS_MAC_CFG_INVERSE_FILTERING;
    }

    if( MAC_BITBAND->CSR6_PB != 0u ) {
        configuration |= MSS_MAC_CFG_PASS_BAD_FRAMES;
    }

    if( MAC_BITBAND->CSR6_HO != 0u ) {
        configuration |= MSS_MAC_CFG_HASH_ONLY_FILTERING_MODE;
    }

    if( MAC_BITBAND->CSR6_HP != 0u ) {
        configuration |= MSS_MAC_CFG_HASH_PERFECT_RECEIVE_FILTERING_MODE;
    }

    return (int32_t)configuration;
}


/***************************************************************************//**
  Sends a packet from the uIP stack to the Ethernet Controller.
  The MSS_MAC_tx_packet() function is used to send a packet to the MSS Ethernet
  MAC. This function writes uip_len bytes of the packet contained in uip_buf into
  the transmit FIFO and then activates the transmitter for this packet. If space
  is available in the FIFO, the function will return once pac_len bytes of the
  packet have been placed into the FIFO and the transmitter has been started.
  This function will not wait for the transmission to complete.

  @return
    The function returns zero if a timeout occurs otherwise it returns size of the packet.

  @see   MAC_rx_packet()
 */

int32_t
MSS_MAC_tx_packet
(
    unsigned short usLength
)
{
	uint32_t desc;
	unsigned long ulDescriptor;
    int32_t error = MAC_OK;

    configASSERT( uip_buf != NULL_buffer );

	configASSERT( usLength >= 12 );

    if( (g_mss_mac.flags & FLAG_EXCEED_LIMIT) == 0u )
    {
		configASSERT( usLength <= MSS_MAX_PACKET_SIZE );
	}

	taskENTER_CRITICAL();
	{
		/* Check both Tx descriptors are free, meaning the double send has completed. */
		if( ( ( (g_mss_mac.tx_descriptors[ 0 ].descriptor_0) & TDES0_OWN) == TDES0_OWN ) || ( ( (g_mss_mac.tx_descriptors[ 1 ].descriptor_0) & TDES0_OWN) == TDES0_OWN ) )
		{
			error = MAC_BUFFER_IS_FULL;
		}
	}
	taskEXIT_CRITICAL();

	configASSERT( ( g_mss_mac.tx_desc_index == 0 ) );
	
	if( error == MAC_OK )
	{
		/* Ensure nothing is going to get sent until both descriptors are ready.
		This is done to	prevent a Tx end occurring prior to the second descriptor
		being ready. */
		MAC_BITBAND->CSR6_ST = 0u;

		/* Assumed TX_RING_SIZE == 2.  A #error directive checks this is the
		case. */
		taskENTER_CRITICAL();
		{
			for( ulDescriptor = 0; ulDescriptor < TX_RING_SIZE; ulDescriptor++ )
			{
				g_mss_mac.tx_descriptors[ g_mss_mac.tx_desc_index ].descriptor_1 = 0u;
	
				if( (g_mss_mac.flags & FLAG_CRC_DISABLE) != 0u ) {
					g_mss_mac.tx_descriptors[ g_mss_mac.tx_desc_index ].descriptor_1 |= TDES1_AC;
				}
	
				/* Every buffer can hold a full frame so they are always first and last
				   descriptor */
				g_mss_mac.tx_descriptors[ g_mss_mac.tx_desc_index ].descriptor_1 |= TDES1_LS | TDES1_FS;
	
				/* set data size */
				g_mss_mac.tx_descriptors[ g_mss_mac.tx_desc_index ].descriptor_1 |= usLength;
	
				/* reset end of ring */
				g_mss_mac.tx_descriptors[TX_RING_SIZE-1].descriptor_1 |= TDES1_TER;
	
				if( usLength > MSS_TX_BUFF_SIZE ) /* FLAG_EXCEED_LIMIT */
				{
					usLength = (uint16_t)MSS_TX_BUFF_SIZE;
				}
	
				/* The data buffer is assigned to the Tx descriptor. */
				g_mss_mac.tx_descriptors[ g_mss_mac.tx_desc_index ].buffer_1 = ( unsigned long ) uip_buf;
	
				/* update counters */
				desc = g_mss_mac.tx_descriptors[ g_mss_mac.tx_desc_index ].descriptor_0;
				if( (desc & TDES0_LO) != 0u ) {
					g_mss_mac.statistics.tx_loss_of_carrier++;
				}
				if( (desc & TDES0_NC) != 0u ) {
					g_mss_mac.statistics.tx_no_carrier++;
				}
				if( (desc & TDES0_LC) != 0u ) {
					g_mss_mac.statistics.tx_late_collision++;
				}
				if( (desc & TDES0_EC) != 0u ) {
					g_mss_mac.statistics.tx_excessive_collision++;
				}
				if( (desc & TDES0_UF) != 0u ) {
					g_mss_mac.statistics.tx_underflow_error++;
				}
				g_mss_mac.statistics.tx_collision_count +=
					(desc >> TDES0_CC_OFFSET) & TDES0_CC_MASK;
	
				/* Give ownership of descriptor to the MAC */
				g_mss_mac.tx_descriptors[ g_mss_mac.tx_desc_index ].descriptor_0 = TDES0_OWN;
				
				g_mss_mac.tx_desc_index = (g_mss_mac.tx_desc_index + 1u) % (uint32_t)TX_RING_SIZE;
			}		
		}
		taskEXIT_CRITICAL();
    }
	
    if (error == MAC_OK)
    {
        error = (int32_t)usLength;
		
		/* Start sending now both descriptors are set up.  This is done to
		prevent a Tx end occurring prior to the second descriptor being
		ready. */
		MAC_BITBAND->CSR6_ST = 1u;
		MAC->CSR1 = 1u;
		
		/* The buffer pointed to by uip_buf is now assigned to a Tx descriptor.
		Find anothere free buffer for uip_buf. */
		uip_buf = MAC_obtain_buffer();
    }
    else
    {
        error = 0;
    }
    return ( error );
}


/***************************************************************************//**
 * Returns available packet size.
 *
 * @param instance      Pointer to a MAC_instance_t structure
 * @return              size of packet, bigger than 0, if a packet is available.
 *                      If not, returns 0.
 * @see   MAC_rx_packet()
 */
int32_t
MSS_MAC_rx_pckt_size
(
    void
)
{
    int32_t retval;
    MAC_dismiss_bad_frames();

    if( (g_mss_mac.rx_descriptors[ g_mss_mac.rx_desc_index ].descriptor_0 &	RDES0_OWN) != 0u )
    {
    	/* Current descriptor is empty */
    	retval = 0;
    }
    else
    {
        uint32_t frame_length;
        frame_length = ( g_mss_mac.rx_descriptors[ g_mss_mac.rx_desc_index ].descriptor_0 >> RDES0_FL_OFFSET ) & RDES0_FL_MASK;
        retval = (int32_t)( frame_length );
    }
    return retval;
}


/***************************************************************************//**
 * Receives a packet from the Ethernet Controller into the uIP stack.
 * This function reads a packet from the receive FIFO of the controller and
 * places it into uip_buf.

 * @return              Size of packet if packet fits in uip_buf.
 * 					    0 if there is no received packet.
 * @see   MAC_rx_pckt_size()
 * @see   MAC_tx_packet()
 */
int32_t
MSS_MAC_rx_packet
(
	void
)
{
	uint16_t frame_length=0u;

    MAC_dismiss_bad_frames();

    if( (g_mss_mac.rx_descriptors[ g_mss_mac.rx_desc_index ].descriptor_0 & RDES0_OWN) == 0u )
    {
        frame_length = ( (
    	    g_mss_mac.rx_descriptors[ g_mss_mac.rx_desc_index ].descriptor_0 >>
    	    RDES0_FL_OFFSET ) & RDES0_FL_MASK );

        /* strip crc */
        frame_length -= 4u;

        if( frame_length > macBUFFER_SIZE ) {
        	return MAC_NOT_ENOUGH_SPACE;
        }

		/* uip_buf is about to point to the buffer that contains the received
		data, mark the buffer that uip_buf is currently pointing to as free
		again. */
		MAC_release_buffer( uip_buf );
        uip_buf = ( unsigned char * ) g_mss_mac.rx_descriptors[ g_mss_mac.rx_desc_index ].buffer_1;
		
		/* The buffer the Rx descriptor was pointing to is now in use by the
		uIP stack - allocate a new buffer to the Rx descriptor. */
		g_mss_mac.rx_descriptors[ g_mss_mac.rx_desc_index ].buffer_1 = ( unsigned long ) MAC_obtain_buffer();

        MSS_MAC_prepare_rx_descriptor();
    }
    return ((int32_t)frame_length);
}


/***************************************************************************//**
 * Receives a packet from the Ethernet Controller.
 * This function reads a packet from the receive FIFO of the controller and
 * sets the address of pacData to the received data.
 * If time_out parameter is zero the function will return
 * immediately (after the copy operation if data is available. Otherwise the function
 * will keep trying to read till time_out expires or data is read, if MSS_MAC_BLOCKING
 * value is given as time_out, function will wait for the reception to complete.
 *
  * @param pacData       The pointer to the packet data.
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
MSS_MAC_rx_packet_ptrset
(
    uint8_t **pacData,
    uint32_t time_out
)
{
	uint16_t frame_length = 0u;
    int8_t exit = 0;

    configASSERT(  (time_out == MSS_MAC_BLOCKING) ||
    			(time_out == MSS_MAC_NONBLOCKING) ||
    			((time_out >= 1) && (time_out <= 0x01000000UL)) );

    MAC_dismiss_bad_frames();

    /* wait for a packet */
	if( time_out != MSS_MAC_BLOCKING ) {
		if( time_out == MSS_MAC_NONBLOCKING ) {
    		MAC_set_time_out( 0u );
		} else {
    		MAC_set_time_out( time_out );
		}
	}

    while( ((g_mss_mac.rx_descriptors[ g_mss_mac.rx_desc_index ].descriptor_0 &
    	RDES0_OWN) != 0u) && (exit == 0) )
    {
    	if( time_out != MSS_MAC_BLOCKING )
    	{
    		if( MAC_get_time_out() == 0u ) {
    			exit = 1;
    		}
    	}
    }

    if(exit == 0)
    {
        frame_length = ( (
    	    g_mss_mac.rx_descriptors[ g_mss_mac.rx_desc_index ].descriptor_0 >>
    	    RDES0_FL_OFFSET ) & RDES0_FL_MASK );

        /* strip crc */
        frame_length -= 4u;

       /* Here we are setting the buffer 'pacData' address to the address
          RX descriptor address. After this is called, the following function
          must be called 'MAC_prepare_rx_descriptor'
          to prepare the current rx descriptor for receiving the next packet.
       */
    	*pacData = (uint8_t *)g_mss_mac.rx_descriptors[ g_mss_mac.rx_desc_index ].buffer_1 ;

    }
    return ((int32_t)frame_length);
}

/***************************************************************************//**
 * Returns the status of connection.
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
)
{
	uint32_t link;

    link = PHY_link_status();
    if( link == MSS_MAC_LINK_STATUS_LINK ) {
    	link |= PHY_link_type();
    }

    return ((int32_t)link);
}


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
)
{
	int32_t link;

    PHY_auto_negotiate();

    link = MSS_MAC_link_status();

    if( (link & MSS_MAC_LINK_STATUS_LINK) != 0u ) {
    	int32_t ret;
	    ret = MAC_stop_transmission();
	    MAC_CHECK( ret == MAC_OK, ret );

	    ret = MAC_stop_receiving();
	    MAC_CHECK( ret == MAC_OK, ret );
        MAC_BITBAND->CSR6_TTM = (uint32_t)((((uint32_t)link & MSS_MAC_LINK_STATUS_100MB) != 0u) ? 1u : 0u );
        MAC_BITBAND->CSR6_FD = (uint32_t)((((uint32_t)link & MSS_MAC_LINK_STATUS_FDX) != 0u) ? 1u : 1u );
	    MAC_start_transmission();
	    MAC_start_receiving();
    }

    return link;
}


/***************************************************************************//**
 * Sets mac address. New address must be unicast.
 *
 * @param new_address   Pointer to a MAC_instance_t structure
 * @see   MAC_get_mac_address()
 */
void
MSS_MAC_set_mac_address
(
    const uint8_t *new_address
)
{
    /* Check if the new address is unicast */
    configASSERT( (new_address[0]&1) == 0 );

   	MAC_memcpy( g_mss_mac.mac_address, new_address, 6u );

   	if((g_mss_mac.flags & FLAG_PERFECT_FILTERING) != 0u ) {
		int32_t a;
	   	/* set unused filters to the new mac address */
		for( a=14*6; a>=0; a-=6 ) {
			if( (g_mss_mac.mac_filter_data[a] & 1u) != 0u ) {
				/* Filters with multicast addresses are used */
				a = -1;
			} else {
				MAC_memcpy( &(g_mss_mac.mac_filter_data[a]),
					g_mss_mac.mac_address, 6u );
			}
		}
   	}

   	MAC_send_setup_frame();
}


/***************************************************************************//**
 * Returns mac address.
 *
 * @param address       Pointer to receive the MAC address
 * @see   MAC_set_mac_address()
 */
void
MSS_MAC_get_mac_address
(
    uint8_t *address
)
{
   	MAC_memcpy( address, g_mss_mac.mac_address, 6u );
}


/***************************************************************************//**
 * Sets mac address filters. Addresses must be multicast.
 *
 * @param filter_count  number of addresses
 * @param filters       Pointer to addresses to be filtered
 */
void
MSS_MAC_set_mac_filters
(
	uint16_t filter_count,
	const uint8_t *filters
)
{
    configASSERT( (filter_count==0) || (filters != NULL_buffer) );
    /* Check if the mac addresses is multicast */
    {
    	int32_t a;
    	for( a = 0u; a < filter_count; a++ ) {
    		configASSERT( (filters[a*6]&1) == 1 );
    	}
    }

    if( filter_count <= 15 ){
    	int32_t a;
    	g_mss_mac.flags |= FLAG_PERFECT_FILTERING;

    	/* copy new filters */
    	MAC_memcpy( g_mss_mac.mac_filter_data, filters, (uint32_t)(filter_count*6));

    	/* set unused filters to our mac address */
    	for( a=filter_count; a<15; a++ ) {
   			MAC_memcpy( &(g_mss_mac.mac_filter_data[a*6]),
   				g_mss_mac.mac_address, 6 );
    	}
    } else {
    	int32_t a,b;
    	uint32_t hash;

    	g_mss_mac.flags &= ~FLAG_PERFECT_FILTERING;

    	/* reset hash table */
    	MAC_memset( g_mss_mac.mac_filter_data, 0u, 64u );

    	for( a=0, b=0; a<filter_count; a++, b+=6 ) {
    		hash = mss_ethernet_crc( &(filters[b]), 6 ) & 0x1FF;
    		g_mss_mac.mac_filter_data[ hash / 8 ] |= 1 << (hash & 0x7);
    	}
    }

    MAC_send_setup_frame();
}


/***************************************************************************//**
 * MAC interrupt service routine.
 *
 * @param instance      Pointer to a MAC_instance_t structure
 * @see   MAC_set_callback()
 */
#if defined(__GNUC__)
__attribute__((__interrupt__)) void EthernetMAC_IRQHandler( void )
#else
void EthernetMAC_IRQHandler( void )
#endif
{
    uint32_t events;
    uint32_t intr_status;

    events = 0u;
    intr_status = MAC->CSR5;

    if( (intr_status & CSR5_NIS_MASK) != 0u ) {
    	if( (intr_status & CSR5_TI_MASK) != 0u ) { /* Transmit */
    		g_mss_mac.statistics.tx_interrupts++;
    		events |= MSS_MAC_EVENT_PACKET_SEND;
    	}

    	if( (intr_status & CSR5_RI_MASK) != 0u ) { /* Receive */
    		g_mss_mac.statistics.rx_interrupts++;
    		events |= MSS_MAC_EVENT_PACKET_RECEIVED;
    	}
    }

    /* Clear interrupts */
    MAC->CSR5 = CSR5_INT_BITS;

    if( (events != 0u) && (g_mss_mac.listener != NULL_callback) ) {
        g_mss_mac.listener( events );
    }
}


/***************************************************************************//**
 * Sets MAC event listener.
 * Sets the given event listener function to be triggered inside MAC_isr().
 * Assigning NULL pointer as the listener function will disable it.
 *
 * @param instance      Pointer to a MAC_instance_t structure
 * @param listener      function pointer to a MAC_callback_t function
 * @return              #MAC_OK if everything is OK
 *                      #MAC_WRONG_PARAMETER if instance is null or hasn't been
 * 						initialized.
 * @see   MAC_isr()
 */
void
MSS_MAC_set_callback
(
    MSS_MAC_callback_t listener
)
{
	/* disable tx and rx interrupts */
    MAC_BITBAND->CSR7_RIE = 0u;
    MAC_BITBAND->CSR7_TIE = 0u;

    g_mss_mac.listener = listener;

	if( listener != NULL_callback ) {
		/* enable tx and rx interrupts */
        MAC_BITBAND->CSR7_RIE = 1u;
        MAC_BITBAND->CSR7_TIE = 1u;
	}
}


/***************************************************************************//**
 * Returns description of last error.
 *
 * @param instance      Pointer to a MAC_instance_t structure
 * @return              A string describing the error. This string must not be
 * 						modified by the application.
 *                      #MAC_WRONG_PARAMETER if instance is null or hasn't been
 *                      initialized.
 */
const int8_t*
MSS_MAC_last_error
(
    void
)
{
	int8_t error_msg_nb;
    const int8_t* returnvalue;

	error_msg_nb = -(g_mss_mac.last_error);
	if( error_msg_nb >= ERROR_MESSAGE_COUNT ) {
		returnvalue = unknown_error;
	} else {
		returnvalue = ErrorMessages[error_msg_nb];
	}
	return returnvalue;
}


/***************************************************************************//**
 * Returns statistics counter of stat_id identifier.
 *
 * @param instance      Pointer to a MAC_instance_t structure
 * @param stat_id		Identifier of statistics counter.
 * @return				Statistics counter of stat_id identifier.
 * 						On error returns 0.
 */
uint32_t
MSS_MAC_get_statistics
(
    mss_mac_statistics_id_t stat_id
)
{
    uint32_t returnval = 0u;

	switch( stat_id ) {
	case MSS_MAC_RX_INTERRUPTS:
		returnval = g_mss_mac.statistics.rx_interrupts;
        break;
	case MSS_MAC_RX_FILTERING_FAIL:
		returnval = g_mss_mac.statistics.rx_filtering_fail;
        break;
	case MSS_MAC_RX_DESCRIPTOR_ERROR:
		returnval = g_mss_mac.statistics.rx_descriptor_error;
        break;
	case MSS_MAC_RX_RUNT_FRAME:
		returnval = g_mss_mac.statistics.rx_runt_frame;
        break;
	case MSS_MAC_RX_NOT_FIRST:
		returnval = g_mss_mac.statistics.rx_not_first;
        break;
	case MSS_MAC_RX_NOT_LAST:
		returnval = g_mss_mac.statistics.rx_not_last;
        break;
	case MSS_MAC_RX_FRAME_TOO_LONG:
		returnval = g_mss_mac.statistics.rx_frame_too_long;
        break;
	case MSS_MAC_RX_COLLISION_SEEN:
		returnval = g_mss_mac.statistics.rx_collision_seen;
        break;
	case MSS_MAC_RX_CRC_ERROR:
		returnval = g_mss_mac.statistics.rx_crc_error;
        break;
	case MSS_MAC_RX_FIFO_OVERFLOW:
		returnval = g_mss_mac.statistics.rx_fifo_overflow;
        break;
	case MSS_MAC_RX_MISSED_FRAME:
		returnval = g_mss_mac.statistics.rx_missed_frame;
        break;
	case MSS_MAC_TX_INTERRUPTS:
		returnval = g_mss_mac.statistics.tx_interrupts;
        break;
	case MSS_MAC_TX_LOSS_OF_CARRIER:
		returnval = g_mss_mac.statistics.tx_loss_of_carrier;
        break;
	case MSS_MAC_TX_NO_CARRIER:
		returnval = g_mss_mac.statistics.tx_no_carrier;
        break;
	case MSS_MAC_TX_LATE_COLLISION:
		returnval = g_mss_mac.statistics.tx_late_collision;
        break;
	case MSS_MAC_TX_EXCESSIVE_COLLISION:
		returnval = g_mss_mac.statistics.tx_excessive_collision;
        break;
	case MSS_MAC_TX_COLLISION_COUNT:
		returnval = g_mss_mac.statistics.tx_collision_count;
        break;
	case MSS_MAC_TX_UNDERFLOW_ERROR:
		returnval = g_mss_mac.statistics.tx_underflow_error;
        break;
    default:
        break;
	}

	return returnval;
}


/**************************** INTERNAL FUNCTIONS ******************************/


/***************************************************************************//**
 * Prepares current rx descriptor for receiving.
 */
void
MSS_MAC_prepare_rx_descriptor
(
    void
)
{
	uint32_t desc;

	/* update counters */
	desc = g_mss_mac.rx_descriptors[ g_mss_mac.rx_desc_index ].descriptor_0;
	if( (desc & RDES0_FF) != 0u ) {
		g_mss_mac.statistics.rx_filtering_fail++;
	}
	if( (desc & RDES0_DE) != 0u ) {
		g_mss_mac.statistics.rx_descriptor_error++;
	}
	if( (desc & RDES0_RF) != 0u ) {
		g_mss_mac.statistics.rx_runt_frame++;
	}
	if( (desc & RDES0_FS) == 0u ) {
		g_mss_mac.statistics.rx_not_first++;
	}
	if( (desc & RDES0_LS) == 0u ) {
		g_mss_mac.statistics.rx_not_last++;
	}
	if( (desc & RDES0_TL) != 0u ) {
		g_mss_mac.statistics.rx_frame_too_long++;
	}
	if( (desc & RDES0_CS) != 0u ) {
		g_mss_mac.statistics.rx_collision_seen++;
	}
	if( (desc & RDES0_CE) != 0u ) {
		g_mss_mac.statistics.rx_crc_error++;
	}

	desc = MAC->CSR8;
	g_mss_mac.statistics.rx_fifo_overflow +=
		(desc & (CSR8_OCO_MASK|CSR8_FOC_MASK)) >> CSR8_FOC_SHIFT;
	g_mss_mac.statistics.rx_missed_frame +=
		(desc & (CSR8_MFO_MASK|CSR8_MFC_MASK));

	/* Give ownership of descriptor to the MAC */
	g_mss_mac.rx_descriptors[ g_mss_mac.rx_desc_index ].descriptor_0 = RDES0_OWN;
	g_mss_mac.rx_desc_index = (g_mss_mac.rx_desc_index + 1u) % RX_RING_SIZE;

	/* Start receive */
    MAC_start_receiving();
}


/***************************************************************************//**
 * Prepares a setup frame and sends it to MAC.
 * This function is blocking.
 * @return		#MAC_OK if everything is ok.
 * 				#MAC_TIME_OUT if timed out before packet send.
 */
static int32_t
MAC_send_setup_frame
(
    void
)
{
	volatile MAC_descriptor_t descriptor;
	uint8_t	frame_data[192];
	uint8_t *data;
	int32_t a,b,c,d;
	int32_t ret;

    /* prepare descriptor */
	descriptor.descriptor_0 = TDES0_OWN;
	descriptor.descriptor_1 = TDES1_SET | TDES1_TER |
		(sizeof(frame_data) << TDES1_TBS1_OFFSET);

	if( (g_mss_mac.flags & FLAG_PERFECT_FILTERING) == 0u ) {
		descriptor.descriptor_1 |= TDES1_FT0;
	}

	descriptor.buffer_1 = (uint32_t)frame_data;
	descriptor.buffer_2 = 0u;

    /* prepare frame */
    if( (g_mss_mac.flags & FLAG_PERFECT_FILTERING) != 0u ) {
    	b = 0;
    	d = 12;
    	c = 90;
    } else {
    	b = 156;
    	d = 0;
    	c = 64;
    }

   	data = g_mss_mac.mac_address;
   	frame_data[b] = data[0];
   	frame_data[b+1] = data[1];
   	frame_data[b+4] = data[2];
   	frame_data[b+5] = data[3];
   	frame_data[b+8] = data[4];
   	frame_data[b+9] = data[5];

   	data = g_mss_mac.mac_filter_data;
    for( a = 0; a < c; ) {
		frame_data[d] = data[a++];
	   	frame_data[d+1] = data[a++];
	   	frame_data[d+4] = data[a++];
	   	frame_data[d+5] = data[a++];
	   	frame_data[d+8] = data[a++];
	   	frame_data[d+9] = data[a++];
	   	d += 12;
	}

	/* Stop transmission */
    ret = MAC_stop_transmission();
    configASSERT( ret == MAC_OK );

    ret = MAC_stop_receiving();
    configASSERT( ret == MAC_OK );

    /* Set descriptor */
    MAC->CSR4 = (uint32_t)&descriptor;

	/* Start transmission */
    MAC_start_transmission();

    /* Wait until transmission over */
    ret = MAC_OK;
    MAC_set_time_out( (uint32_t)SETUP_FRAME_TIME_OUT );

    while( (((MAC->CSR5 & CSR5_TS_MASK) >> CSR5_TS_SHIFT) !=
    	CSR5_TS_SUSPENDED) && (MAC_OK == ret) )
    {
    	/* transmit poll demand */
    	MAC->CSR1 = 1u;
    	if( MAC_get_time_out() == 0u ) {
    		ret = MAC_TIME_OUT;
    	}
    }

	MAC_CHECK( MAC_stop_transmission() == MAC_OK, MAC_FAIL );

    /* Set tx descriptor */
    MAC->CSR4 = (uint32_t)g_mss_mac.tx_descriptors;

    /* Start receiving and transmission */
    MAC_start_receiving();
    MAC_start_transmission();

    return ret;
}


/***************************************************************************//**
 * Stops transmission.
 * Function will wait until transmit operation enters stop state.
 *
 * @return			#MAC_OK if everything is ok.
 * 					#MAC_TIME_OUT if timed out.
 */
static int32_t
MAC_stop_transmission
(
    void
)
{
    int32_t retval = MAC_OK;
    MAC_set_time_out( (uint16_t)STATE_CHANGE_TIME_OUT );

	while( (((MAC->CSR5 & CSR5_TS_MASK) >> CSR5_TS_SHIFT) !=
		CSR5_TS_STOPPED) && (retval == MAC_OK) )
	{
    	MAC_BITBAND->CSR6_ST = 0u;
    	if( MAC_get_time_out() == 0u ) {
    		retval = MAC_TIME_OUT;
    	}
	}
	return retval;
}


/***************************************************************************//**
 * Starts transmission.
 */
static void
MAC_start_transmission
(
    void
)
{
    MAC_BITBAND->CSR6_ST = 1u;
}


/***************************************************************************//**
 * Stops transmission.
 * Function will wait until transmit operation enters stop state.
 *
 * @return			#MAC_OK if everything is ok.
 * 					#MAC_TIME_OUT if timed out.
 */
static int32_t
MAC_stop_receiving
(
    void
)
{
    int32_t retval = MAC_OK;
    MAC_set_time_out( (uint16_t)STATE_CHANGE_TIME_OUT );

	while( (((MAC->CSR5 & CSR5_RS_MASK) >> CSR5_RS_SHIFT) != CSR5_RS_STOPPED)
            && (retval == MAC_OK) )
	{
    	MAC_BITBAND->CSR6_SR = 0u;
    	if( MAC_get_time_out() == 0u ) {
    		retval = MAC_TIME_OUT;
    	}
	}

	return retval;
}


/***************************************************************************//**
 * Starts transmission.
 */
static void
MAC_start_receiving
(
    void
)
{
    MAC_BITBAND->CSR6_SR = 1u;
}


/***************************************************************************//**
 * Dismisses bad frames.
 *
 * @return		dismissed frame count.
 */
static int32_t
MAC_dismiss_bad_frames
(
    void
)
{
	int32_t dc = 0;
	int8_t cont = 1;

	if( MAC_BITBAND->CSR6_PB != 0u ) {
		/* User wants bad frames too, don't dismiss anything */
		cont = 0;
	}

	while( ( (g_mss_mac.rx_descriptors[ g_mss_mac.rx_desc_index ].descriptor_0 &
            RDES0_OWN) == 0u) && (cont == 1) ) /* Host owns this descriptor */
    {
    	/* check error summary */
    	if( (g_mss_mac.rx_descriptors[ g_mss_mac.rx_desc_index ].descriptor_0 &
    		(RDES0_ES | RDES0_LS | RDES0_FS)) != (RDES0_LS | RDES0_FS) )
    	{
    		MSS_MAC_prepare_rx_descriptor();
    		dc++;
    	}
        else
        {
    		cont = 0;
    	}
    }

	return dc;
}

/***************************************************************************//**
 * Sets time out value.
 * #MAC_get_time_out must be called frequently to make time out value updated.
 * Because of user may not be using ISR, we can not update time out in ISR.
 *
 * @time_out	time out value in milli seconds.
 * 				Must be smaller than 0x01000000.
 */
static void
MAC_set_time_out
(
    uint32_t time_out
)
{
	g_mss_mac.time_out_value = (time_out * 122u) / 10u;

	g_mss_mac.last_timer_value = (uint16_t)( MAC->CSR11 & CSR11_TIM_MASK );
}

/***************************************************************************//**
 * Returns time out value.
 *
 * @return		timer out value in milli seconds.
 */
static uint32_t
MAC_get_time_out
(
    void
)
{
	uint32_t timer;
	uint32_t time = 0u;

	timer = ( MAC->CSR11 & CSR11_TIM_MASK );

	if( timer > g_mss_mac.last_timer_value ) {
		time = 0x0000ffffUL;
	}
	time += g_mss_mac.last_timer_value - timer;

	if( MAC_BITBAND->CSR6_TTM == 0u ) {
		time *= 10u;
	}
	if( g_mss_mac.time_out_value <= time ){
		g_mss_mac.time_out_value = 0u;
	} else {
		g_mss_mac.time_out_value -= time;
	}

	g_mss_mac.last_timer_value = (uint16_t)timer;

	return ((g_mss_mac.time_out_value * 10u) / 122u);
}

/***************************************************************************//**
 * Fills the first n bytes of the memory area pointed to by s with the constant
 * byte c.
 */
static void MAC_memset(uint8_t *s, uint8_t c, uint32_t n)
{
    uint8_t *sb = s;

    while( n > 0u ) {
    	n--;
        sb[n] = c;
    }
}

/***************************************************************************//**
 * Fills all fields of MAC_instance_t with c.
 *
 * @return          a pointer to the given MAC_instance_t s.
 */
static void MAC_memset_All(MAC_instance_t *s, uint32_t c)
{
    int32_t count;
    s->base_address = (addr_t)c;
    s->flags = (uint8_t)c;
    s->last_error = (int8_t)c;
    s->last_timer_value = (uint16_t)c;
    s->listener = NULL_callback;
   	MAC_memset( s->mac_address, (uint8_t)c, 6u );
   	MAC_memset( s->mac_filter_data, (uint8_t)c, 90u );
    s->phy_address = (uint8_t)c;
    s->rx_desc_index =c;
    for(count = 0; count<RX_RING_SIZE ;count++)
    {
        s->rx_descriptors[count].buffer_1 = c;
        s->rx_descriptors[count].buffer_2 = c;
        s->rx_descriptors[count].descriptor_0 = c;
        s->rx_descriptors[count].descriptor_1 = c;
    }
    s->statistics.rx_collision_seen =c;
    s->statistics.rx_crc_error = c;
    s->statistics.rx_descriptor_error = c;
    s->statistics.rx_fifo_overflow = c;
    s->statistics.rx_filtering_fail = c;
    s->statistics.rx_frame_too_long = c;
    s->statistics.rx_interrupts = c;
    s->statistics.rx_missed_frame = c;
    s->statistics.rx_not_first = c;
    s->statistics.rx_not_last = c;
    s->statistics.rx_runt_frame = c;
    s->statistics.tx_collision_count = c;
    s->statistics.tx_excessive_collision = c;
    s->statistics.tx_interrupts = c;
    s->statistics.tx_late_collision = c;
    s->statistics.tx_loss_of_carrier = c;
    s->statistics.tx_no_carrier = c;
    s->statistics.tx_underflow_error = c;
    s->time_out_value = c;
    s->tx_desc_index = c;
    for(count = 0; count < TX_RING_SIZE ;count++)
    {
        s->tx_descriptors[count].buffer_1 = c;
        s->tx_descriptors[count].buffer_2 = c;
        s->tx_descriptors[count].descriptor_0 = c;
        s->tx_descriptors[count].descriptor_1 = c;
    }
}

/***************************************************************************//**
 * Copies n bytes from memory area src to memory area dest.
 * The memory areas should not overlap.
 *
 * @return          a pointer to the memory area dest.
 */
static void MAC_memcpy(uint8_t *dest, const uint8_t *src, uint32_t n)
{
    uint8_t *d = dest;

    while( n > 0u ) {
    	n--;
        d[n] = src[n];
    }
}

/***************************************************************************//**
 * Tx has completed, mark the buffers that were assigned to the Tx descriptors
 * as free again.
 *
 */
void MSS_MAC_FreeTxBuffers( void )
{
	/* Check the buffers have not already been freed in the first of the
	two Tx interrupts - which could potentially happen if the second Tx completed
	during the interrupt for the first Tx. */
	if( g_mss_mac.tx_descriptors[ 0 ].buffer_1 != ( uint32_t ) NULL )
	{
		if( ( ( (g_mss_mac.tx_descriptors[ 0 ].descriptor_0) & TDES0_OWN) == 0 ) && ( ( (g_mss_mac.tx_descriptors[ 1 ].descriptor_0) & TDES0_OWN) == 0 ) )
		{
			configASSERT( g_mss_mac.tx_descriptors[ 0 ].buffer_1 == g_mss_mac.tx_descriptors[ 1 ].buffer_1 );
			MAC_release_buffer( ( unsigned char * ) g_mss_mac.tx_descriptors[ 0 ].buffer_1 );
			
			/* Just to mark the fact that the buffer has already been released. */
			g_mss_mac.tx_descriptors[ 0 ].buffer_1 = ( uint32_t ) NULL;
		}
	}
}

/***************************************************************************//**
 * Look through the array of buffers until one is found that is free for use -
 * that is, not currently assigned to an Rx or a Tx descriptor.  Mark the buffer
 * as in use, then return its address.
 *
 * @return          a pointer to a free buffer.
 */
unsigned char *MAC_obtain_buffer( void )
{
long lIndex, lAttempt = 0, lDescriptor, lBufferIsInUse;
unsigned char *pcReturn = NULL;
unsigned char *pcBufferAddress;

	/* Find and return the address of a buffer that is not being used.  Mark
	the buffer as now in use. */
	while( ( lAttempt <= 1 ) && ( pcReturn == NULL ) )
	{
		for( lIndex = 0; lIndex < macNUM_BUFFERS; lIndex++ )
		{
			if( ucMACBufferInUse[ lIndex ] == pdFALSE )
			{
				pcReturn = &( xMACBuffers.ucBuffer[ lIndex ][ 0 ] );
				ucMACBufferInUse[ lIndex ] = pdTRUE;
				break;
			}
		}
		
		if( pcReturn == NULL )
		{
			/* Did not find a buffer.  That should not really happen, but could if
			an interrupt was missed.  See if any buffers are marked as in use, but
			are not actually in use. */
			for( lIndex = 0; lIndex < macNUM_BUFFERS; lIndex++ )
			{
				pcBufferAddress = &( xMACBuffers.ucBuffer[ lIndex ][ 0 ] );
				lBufferIsInUse = pdFALSE;
				
				/* Is the buffer used by an Rx descriptor? */
				for( lDescriptor = 0; lDescriptor < RX_RING_SIZE; lDescriptor++ )
				{
					if( g_mss_mac.rx_descriptors[ lDescriptor ].buffer_1 == ( uint32_t ) pcBufferAddress )
					{
						/* The buffer is in use by an Rx descriptor. */
						lBufferIsInUse = pdTRUE;
						break;
					}
				}
				
				if( lBufferIsInUse != pdTRUE )
				{
					/* Is the buffer used by an Tx descriptor? */
					for( lDescriptor = 0; lDescriptor < TX_RING_SIZE; lDescriptor++ )
					{
						if( g_mss_mac.tx_descriptors[ lDescriptor ].buffer_1 == ( uint32_t ) pcBufferAddress )
						{
							/* The buffer is in use by an Tx descriptor. */
							lBufferIsInUse = pdTRUE;
							break;
						}
					}			
				}
				
				/* If the buffer was not found to be in use by either a Tx or an
				Rx descriptor, but the buffer is marked as in use, then mark the
				buffer to be in it's correct state of "not in use". */
				if( ( lBufferIsInUse == pdFALSE ) && ( ucMACBufferInUse[ lIndex ] == pdTRUE ) )
				{
					ucMACBufferInUse[ lIndex ] = pdFALSE;
				}
			}
		}
																	
		/* If any buffer states were changed it might be that a buffer can now
		be obtained.  Try again, but only one more time. */
		lAttempt++;
	}
	
	configASSERT( pcReturn );
	return pcReturn;
}

/***************************************************************************//**
 * Return a buffer to the list of free buffers, it was in use, but is not now.
 *
 */
void MAC_release_buffer( unsigned char *pucBufferToRelease )
{
long lIndex;

	/* uip_buf is going to point to a different buffer - first ensure the buffer
	it is currently pointing to is marked as being free again. */
	for( lIndex = 0; lIndex < macNUM_BUFFERS; lIndex++ )
	{
		if( pucBufferToRelease == &( xMACBuffers.ucBuffer[ lIndex ][ 0 ] ) )
		{
			/* This is the buffer in use, mark it as being free. */
			ucMACBufferInUse[ lIndex ] = pdFALSE;
			break;
		}
	}
	
	configASSERT( lIndex < macNUM_BUFFERS );
}



#ifdef __cplusplus
}
#endif

/******************************** END OF FILE *********************************/

