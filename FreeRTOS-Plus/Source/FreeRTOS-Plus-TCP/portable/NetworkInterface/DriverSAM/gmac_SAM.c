/**
 * \file
 *
 * \brief GMAC (Ethernet MAC) driver for SAM.
 *
 * Copyright (c) 2015-2016 Atmel Corporation. All rights reserved.
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


/* Standard includes. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>

/* FreeRTOS includes. */
#include "FreeRTOS.h"
#include "task.h"
#include "semphr.h"

#include "FreeRTOSIPConfig.h"

/* FreeRTOS+TCP includes. */
#include "FreeRTOS_IP.h"
#include "FreeRTOS_Sockets.h"
#include "FreeRTOS_IP_Private.h"
#include "FreeRTOS_ARP.h"
#include "NetworkBufferManagement.h"
#include "NetworkInterface.h"

#include "compiler.h"
#include "gmac_SAM.h"

#if( SAME70 != 0 )
	/* This file is included to see if 'CONF_BOARD_ENABLE_CACHE' is defined. */
	#include "conf_board.h"
	#include "core_cm7.h"
#endif

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/// @endcond

#ifndef ARRAY_SIZE
	#define ARRAY_SIZE(x)  (int)( sizeof(x) / sizeof(x)[0] )
#endif

#if( GMAC_RX_BUFFERS <= 1 )
	#error Configuration error
#endif

#if( GMAC_TX_BUFFERS <= 1 )
	#error Configuration error
#endif

/**
 * \defgroup gmac_group Ethernet Media Access Controller
 *
 * See \ref gmac_quickstart.
 *
 * Driver for the GMAC (Ethernet Media Access Controller).
 * This file contains basic functions for the GMAC, with support for all modes, settings
 * and clock speeds.
 *
 * \section dependencies Dependencies
 * This driver does not depend on other modules.
 *
 * @{
 */

#define NETWORK_BUFFER_SIZE		1536

__attribute__ ( ( aligned( 32 ) ) )
__attribute__ ( ( section( ".first_data" ) ) )
	uint8_t ucNetworkPackets[ ipconfigNUM_NETWORK_BUFFER_DESCRIPTORS * NETWORK_BUFFER_SIZE ];

/** TX descriptor lists */
__attribute__ ((section(".first_data")))
COMPILER_ALIGNED(8)
static gmac_tx_descriptor_t gs_tx_desc[ GMAC_TX_BUFFERS ];

#if( SAME70 != 0 )
	__attribute__ ((section(".first_data")))
	COMPILER_ALIGNED(8)
	static gmac_tx_descriptor_t gs_tx_desc_null;
#endif

/** RX descriptors lists */
__attribute__ ((section(".first_data")))
COMPILER_ALIGNED(8)
static gmac_rx_descriptor_t gs_rx_desc[ GMAC_RX_BUFFERS ];

#if( ipconfigZERO_COPY_TX_DRIVER == 0 )
	/** Send Buffer. Section 3.6 of AMBA 2.0 spec states that burst should not cross the
	 * 1K Boundaries. Receive buffer manager write operations are burst of 2 words => 3 lsb bits
	 * of the address shall be set to 0.
	 */
	__attribute__ ((section(".first_data")))
	COMPILER_ALIGNED(8)
	static uint8_t gs_uc_tx_buffer[ GMAC_TX_BUFFERS * GMAC_TX_UNITSIZE ];
#endif /* ipconfigZERO_COPY_TX_DRIVER */

#if( ipconfigZERO_COPY_RX_DRIVER == 0 )
	/** Receive Buffer */
	__attribute__ ((section(".first_data")))
	COMPILER_ALIGNED(8)
	static uint8_t gs_uc_rx_buffer[ GMAC_RX_BUFFERS * GMAC_RX_UNITSIZE ];
#endif /* ipconfigZERO_COPY_RX_DRIVER */

/** Return count in buffer */
#define CIRC_CNT( head, tail, size )		( ( ( head ) - ( tail ) ) % ( size ) )

/*
 * Return space available, from 0 to size-1.
 * Always leave one free char as a completely full buffer that has (head == tail),
 * which is the same as empty.
 */
#define CIRC_SPACE( head, tail, size )		CIRC_CNT( ( tail ), ( ( head ) + 1 ), ( size ) )

/** Circular buffer is empty ? */
#define CIRC_EMPTY( head, tail )			( ( head ) == ( tail ) )
/** Clear circular buffer */
#define CIRC_CLEAR( head, tail )			do { ( head ) = 0; ( tail ) = 0; } while( 0 )

/* Two call-back functions that should be defined in NetworkInterface.c */
extern void xRxCallback( uint32_t ulStatus );
extern void xTxCallback( uint32_t ulStatus, uint8_t *puc_buffer );
extern void returnTxBuffer(uint8_t *puc_buffer);
 

/** Increment head or tail */
static __inline void circ_inc32( int32_t *lHeadOrTail, uint32_t ulSize )
{
	( *lHeadOrTail ) ++;
    if( ( *lHeadOrTail ) >= ( int32_t )ulSize )
	{
		( *lHeadOrTail ) = 0;
	}
}

/**
 * \brief Wait PHY operation to be completed.
 *
 * \param p_gmac HW controller address.
 * \param ul_retry The retry times, 0 to wait forever until completeness.
 *
 * Return GMAC_OK if the operation is completed successfully.
 */
uint8_t gmac_wait_phy(Gmac* p_gmac, const uint32_t ul_retry)
{
	volatile uint32_t ul_retry_count = 0;
	const uint32_t xPHYPollDelay = pdMS_TO_TICKS( 1ul );

	while (!gmac_is_phy_idle(p_gmac)) {
		if (ul_retry == 0) {
			continue;
		}

		ul_retry_count++;

		if (ul_retry_count >= ul_retry) {
			return GMAC_TIMEOUT;
		}

		/* Block the task to allow other tasks to execute while the PHY
		is not connected. */
		vTaskDelay( xPHYPollDelay );
	}
	return GMAC_OK;
}

/**
 * \brief Disable transfer, reset registers and descriptor lists.
 *
 * \param p_dev Pointer to GMAC driver instance.
 *
 */
void gmac_reset_tx_mem(gmac_device_t* p_dev)
{
	Gmac *p_hw = p_dev->p_hw;

	uint32_t ul_index;
	uint32_t ul_address;

	/* Disable TX */
	gmac_enable_transmit(p_hw, 0);

	{
		for( ul_index = 0; ul_index < ARRAY_SIZE(gs_tx_desc); ul_index++ )
		{
		uint32_t ulAddr = gs_tx_desc[ul_index].addr;
			if (ulAddr) {
				returnTxBuffer ((uint8_t *)ulAddr);
			}
		}
	}
	/* Set up the TX descriptors */
	CIRC_CLEAR(p_dev->l_tx_head, p_dev->l_tx_tail);
	for( ul_index = 0; ul_index < GMAC_TX_BUFFERS; ul_index++ )
	{
		#if( ipconfigZERO_COPY_TX_DRIVER != 0 )
		{
			ul_address = (uint32_t) 0u;
		}
		#else
		{
			ul_address = (uint32_t) (&(gs_uc_tx_buffer[ul_index * GMAC_TX_UNITSIZE]));
		}
		#endif /* ipconfigZERO_COPY_TX_DRIVER */
		gs_tx_desc[ul_index].addr = ul_address;
		gs_tx_desc[ul_index].status.val = GMAC_TXD_USED;
	}
	/* Set the WRAP bit in the last descriptor. */
	gs_tx_desc[GMAC_TX_BUFFERS - 1].status.val = GMAC_TXD_USED | GMAC_TXD_WRAP;

	/* Set transmit buffer queue */
	gmac_set_tx_queue(p_hw, (uint32_t) gs_tx_desc);
	#if( SAME70 != 0 )
	{
		gmac_set_tx_priority_queue(p_hw, (uint32_t)&gs_tx_desc_null, GMAC_QUE_1);
		gmac_set_tx_priority_queue(p_hw, (uint32_t)&gs_tx_desc_null, GMAC_QUE_2);
		/* Note that SAME70 REV B had 6 priority queues. */
		gmac_set_tx_priority_queue(p_hw, (uint32_t)&gs_tx_desc_null, GMAC_QUE_3);
		gmac_set_tx_priority_queue(p_hw, (uint32_t)&gs_tx_desc_null, GMAC_QUE_4);
		gmac_set_tx_priority_queue(p_hw, (uint32_t)&gs_tx_desc_null, GMAC_QUE_5);
	}
	#endif
}

/**
 * \brief Disable receiver, reset registers and descriptor list.
 *
 * \param p_dev Pointer to GMAC Driver instance.
 */
static void gmac_reset_rx_mem(gmac_device_t* p_dev)
{
	Gmac *p_hw = p_dev->p_hw;

	uint32_t ul_index;
	uint32_t ul_address;

	/* Disable RX */
	gmac_enable_receive(p_hw, 0);

	/* Set up the RX descriptors */
	p_dev->ul_rx_idx = 0;
	for( ul_index = 0; ul_index < GMAC_RX_BUFFERS; ul_index++ )
	{
		#if( ipconfigZERO_COPY_RX_DRIVER != 0 )
		{
		NetworkBufferDescriptor_t *pxNextNetworkBufferDescriptor;

			pxNextNetworkBufferDescriptor = pxGetNetworkBufferWithDescriptor( GMAC_RX_UNITSIZE, 0ul );
			configASSERT( pxNextNetworkBufferDescriptor != NULL );
			ul_address = ( uint32_t )( pxNextNetworkBufferDescriptor->pucEthernetBuffer );
		}
		#else
		{
			ul_address = ( uint32_t ) ( &( gs_uc_rx_buffer[ ul_index * GMAC_RX_UNITSIZE ] ) );
		}
		#endif /* ipconfigZERO_COPY_RX_DRIVER */
		gs_rx_desc[ul_index].addr.val = ul_address & GMAC_RXD_ADDR_MASK;
		gs_rx_desc[ul_index].status.val = 0;
	}
	/* Set the WRAP bit in the last descriptor. */
	gs_rx_desc[GMAC_RX_BUFFERS - 1].addr.bm.b_wrap = 1;

	/* Set receive buffer queue */
	gmac_set_rx_queue(p_hw, (uint32_t)gs_rx_desc);
}


/**
 * \brief Initialize the allocated buffer lists for GMAC driver to transfer data.
 * Must be invoked after gmac_dev_init() but before RX/TX starts.
 *
 * \note If input address is not 8-byte aligned, the address is automatically
 *       adjusted and the list size is reduced by one.
 *
 * \param p_gmac Pointer to GMAC instance.
 * \param p_gmac_dev Pointer to GMAC device instance.
 * \param p_dev_mm Pointer to the GMAC memory management control block.
 *
 * \return GMAC_OK or GMAC_PARAM.
 */
static uint8_t gmac_init_mem(Gmac* p_gmac, gmac_device_t* p_gmac_dev)
{
	/* Assign TX buffers */
#if( ipconfigZERO_COPY_TX_DRIVER == 0 )
	if ((((uint32_t) gs_uc_tx_buffer) & 0x7)
			|| ((uint32_t) p_dev_mm->p_tx_dscr & 0x7)) {
		p_dev_mm->ul_tx_size--;
	}
	p_gmac_dev->p_tx_buffer =
			(uint8_t *) (((uint32_t) gs_uc_tx_buffer) & 0xFFFFFFF8);
#endif

	/* Reset TX & RX Memory */
	gmac_reset_rx_mem(p_gmac_dev);
	gmac_reset_tx_mem(p_gmac_dev);

	/* Enable Rx and Tx, plus the statistics register */
	gmac_enable_transmit(p_gmac, true);
	gmac_enable_receive(p_gmac, true);
	gmac_enable_statistics_write(p_gmac, true);

	/* Set up the interrupts for transmission and errors */
	gmac_enable_interrupt(p_gmac,
			GMAC_IER_RLEX  | /* Enable retry limit  exceeded interrupt. */
			GMAC_IER_RXUBR | /* Enable receive used bit read interrupt. */
			GMAC_IER_ROVR  | /* Enable receive overrun interrupt. */
			GMAC_IER_TCOMP | /* Enable transmit complete interrupt. */
			GMAC_IER_TUR   | /* Enable transmit underrun interrupt. */
			GMAC_IER_TFC   | /* Enable transmit buffers exhausted in mid-frame interrupt. */
			GMAC_IER_HRESP | /* Enable Hresp not OK interrupt. */
			GMAC_IER_PFNZ  | /* Enable pause frame received interrupt. */
			GMAC_IER_PTZ   | /* Enable pause time zero interrupt. */
			GMAC_IER_RCOMP);  /* Enable receive complete interrupt. */

	return GMAC_OK;
}

/**
 * \brief Initialize the GMAC driver.
 *
 * \param p_gmac   Pointer to the GMAC instance.
 * \param p_gmac_dev Pointer to the GMAC device instance.
 * \param p_opt GMAC configure options.
 */
void gmac_dev_init(Gmac* p_gmac, gmac_device_t* p_gmac_dev,
		gmac_options_t* p_opt)
{
	/* Disable TX & RX and more */
	gmac_network_control(p_gmac, 0);
	gmac_disable_interrupt(p_gmac, ~0u);

	gmac_clear_statistics(p_gmac);

	/* Clear all status bits in the receive status register. */
	gmac_clear_rx_status(p_gmac, GMAC_RSR_RXOVR | GMAC_RSR_REC | GMAC_RSR_BNA
			| GMAC_RSR_HNO);

#ifndef GMAC_TSR_UND
	/* GMAC_TSR_UND is only defined by SAM4E. */
	#define GMAC_TSR_UND    0ul
#endif
	/* Clear all status bits in the transmit status register */
	gmac_clear_tx_status(p_gmac, GMAC_TSR_UBR | GMAC_TSR_COL | GMAC_TSR_RLE
			| GMAC_TSR_TFC | GMAC_TSR_TXCOMP | GMAC_TSR_UND);

	/* Clear interrupts */
	gmac_get_interrupt_status(p_gmac);
#if !defined(ETHERNET_CONF_DATA_OFFSET)
	/*  Receive Buffer Offset
	 * Indicates the number of bytes by which the received data
	 * is offset from the start of the receive buffer
	 * which can be handy for alignment reasons */
	/* Note: FreeRTOS+TCP wants to have this offset set to 2 bytes */
	#error ETHERNET_CONF_DATA_OFFSET not defined, assuming 0
#endif
	/* Enable the copy of data into the buffers
	   ignore broadcasts, and not copy FCS. */

	gmac_set_config(p_gmac,
			( gmac_get_config(p_gmac) & ~GMAC_NCFGR_RXBUFO_Msk ) |
			GMAC_NCFGR_RFCS |   /*  Remove FCS, frame check sequence (last 4 bytes) */
			GMAC_NCFGR_PEN |    /* Pause Enable */
			GMAC_NCFGR_RXBUFO( ETHERNET_CONF_DATA_OFFSET ) | /* Set Ethernet Offset  */
			GMAC_RXD_RXCOEN );	/* RXCOEN related function */

	/*
	 * GMAC_DCFGR_TXCOEN: (GMAC_DCFGR) Transmitter Checksum Generation Offload Enable.
	 * Note: SAM4E/SAME70 do have RX checksum offloading
	 * but TX checksum offloading has NOT been implemented,
	 * at least on a SAM4E.
	 * http://community.atmel.com/forum/sam4e-gmac-transmit-checksum-offload-enablesolved
	 */

	{
	uint32_t ulValue = gmac_get_dma(p_gmac);

		/* Let the GMAC set TX checksum's. */
		ulValue |= GMAC_DCFGR_TXCOEN;
		#if( SAME70 != 0 )
		{
			/* Transmitter Packet Buffer Memory Size Select:
			Use full configured addressable space (4 Kbytes). */
			ulValue |= GMAC_DCFGR_TXPBMS;
		}
		#endif

		/* Clear the DMA Receive Buffer Size (DRBS) field: */
		ulValue &= ~( GMAC_DCFGR_DRBS_Msk );
		/* And set it: */
		ulValue |= ( GMAC_RX_UNITSIZE / 64 ) << GMAC_DCFGR_DRBS_Pos;

		gmac_set_dma(p_gmac, ulValue);
	}

	/* Enable/Disable Copy(Receive) All Valid Frames. */		
	gmac_enable_copy_all(p_gmac, p_opt->uc_copy_all_frame);
	
	/* Disable/Enable broadcast receiving */
	gmac_disable_broadcast(p_gmac, p_opt->uc_no_boardcast);


	/* Initialize memory */
	gmac_init_mem(p_gmac, p_gmac_dev);

	/* Set Mac Address */
	gmac_set_address(p_gmac, 0, p_opt->uc_mac_addr);
}

/**
 * \brief Frames can be read from the GMAC in multiple sections.
 *
 * Returns > 0 if a complete frame is available
 * It also it cleans up incomplete older frames
 */

static uint32_t gmac_dev_poll(gmac_device_t* p_gmac_dev)
{
	uint32_t ulReturn = 0;
	int32_t ulIndex = p_gmac_dev->ul_rx_idx;
	gmac_rx_descriptor_t *pxHead = &gs_rx_desc[ulIndex];

//	#warning Just for debugging
//	if((pxHead->addr.val & GMAC_RXD_OWNERSHIP) != 0)
//	{
//		NVIC_DisableIRQ( GMAC_IRQn );
//	}

	#if( ipconfigZERO_COPY_RX_DRIVER == 0 )
	{
		/* Discard any incomplete frames */
		while ((pxHead->addr.val & GMAC_RXD_OWNERSHIP) &&
				(pxHead->status.val & GMAC_RXD_SOF) == 0)
		{
			pxHead->addr.val &= ~(GMAC_RXD_OWNERSHIP);
			circ_inc32 (&ulIndex, GMAC_RX_BUFFERS);
			pxHead = &gs_rx_desc[ulIndex];
			p_gmac_dev->ul_rx_idx = ulIndex;
			#if( GMAC_STATS != 0 )
			{
				gmacStats.incompCount++;
			}
			#endif
		}
	}
	#endif /* ipconfigZERO_COPY_RX_DRIVER == 0 */

	while ((pxHead->addr.val & GMAC_RXD_OWNERSHIP) != 0)
	{
		#if( ipconfigZERO_COPY_RX_DRIVER == 0 )
		{
			if ((pxHead->status.val & GMAC_RXD_EOF) != 0) {
				/* Here a complete frame has been seen with SOF and EOF */
				ulReturn = pxHead->status.bm.b_len;
				break;
			}
			circ_inc32 (&ulIndex, GMAC_RX_BUFFERS);
			pxHead = &gs_rx_desc[ulIndex];
			if ((pxHead->addr.val & GMAC_RXD_OWNERSHIP) == 0) {
				/* CPU is not the owner (yet) */
				break;
			}
			if ((pxHead->status.val & GMAC_RXD_SOF) != 0) {
				/* Strange, we found a new Start Of Frame
				 * discard previous segments */
				int32_t ulPrev = p_gmac_dev->ul_rx_idx;
				pxHead = &gs_rx_desc[ulPrev];
				do {
					pxHead->addr.val &= ~(GMAC_RXD_OWNERSHIP);
					circ_inc32 (&ulPrev, GMAC_RX_BUFFERS);
					pxHead = &gs_rx_desc[ulPrev];
					#if( GMAC_STATS != 0 )
					{
						gmacStats.truncCount++;
					}
					#endif
				} while (ulPrev != ulIndex);
				p_gmac_dev->ul_rx_idx = ulIndex;
			}
		}
		#else /* ipconfigZERO_COPY_RX_DRIVER */
		{
			if ((pxHead->status.val & (GMAC_RXD_SOF|GMAC_RXD_EOF)) == (GMAC_RXD_SOF|GMAC_RXD_EOF)) {
				/* Here a complete frame in a single segment. */
				ulReturn = pxHead->status.bm.b_len;
				break;
			}
			/* Return the buffer to DMA. */
			pxHead->addr.bm.b_ownership = 0;

			/* Let ulIndex/pxHead point to the next buffer. */
			circ_inc32 (&ulIndex, GMAC_RX_BUFFERS);
			pxHead = &gs_rx_desc[ulIndex];
			/* And remember this index. */
			p_gmac_dev->ul_rx_idx = ulIndex;
		}
		#endif /* ipconfigZERO_COPY_RX_DRIVER */
	}
	return ulReturn;
}

/**
 * \brief Frames can be read from the GMAC in multiple sections.
 * Read ul_frame_size bytes from the GMAC receive buffers to pcTo.
 * p_rcv_size is the size of the entire frame.  Generally gmac_read
 * will be repeatedly called until the sum of all the ul_frame_size equals
 * the value of p_rcv_size.
 *
 * \param p_gmac_dev Pointer to the GMAC device instance.
 * \param p_frame Address of the frame buffer.
 * \param ul_frame_size  Length of the frame.
 * \param p_rcv_size   Received frame size.
 *
 * \return GMAC_OK if receiving frame successfully, otherwise failed.
 */
uint32_t gmac_dev_read(gmac_device_t* p_gmac_dev, uint8_t* p_frame,
		uint32_t ul_frame_size, uint32_t* p_rcv_size,
		uint8_t** pp_recv_frame)
{
	int32_t nextIdx;	/* A copy of the Rx-index 'ul_rx_idx' */
	int32_t bytesLeft = gmac_dev_poll (p_gmac_dev);
	gmac_rx_descriptor_t *pxHead;

	if (bytesLeft == 0 )
	{
		return GMAC_RX_NO_DATA;
	}

	/* gmac_dev_poll has confirmed that there is a complete frame at
	 * the current position 'ul_rx_idx'
	 */
	nextIdx = p_gmac_dev->ul_rx_idx;

	/* Read +2 bytes because buffers are aligned at -2 bytes */
	bytesLeft = min( bytesLeft + 2, ( int32_t )ul_frame_size );

#if( __DCACHE_PRESENT != 0 ) && defined( CONF_BOARD_ENABLE_CACHE )
	SCB_InvalidateDCache();
#endif

	#if( ipconfigZERO_COPY_RX_DRIVER == 0 )
	{

		/* The frame will be copied in 1 or 2 memcpy's */
		if( ( p_frame != NULL ) && ( bytesLeft != 0 ) )
		{
		const uint8_t *source;
		int32_t left;
		int32_t toCopy;

			source = gs_uc_rx_buffer + nextIdx * GMAC_RX_UNITSIZE;
			left = bytesLeft;
			toCopy = ( GMAC_RX_BUFFERS - nextIdx ) * GMAC_RX_UNITSIZE;
			if(toCopy > left )
			{
				toCopy = left;
			}
			memcpy (p_frame, source, toCopy);
			left -= toCopy;

			if( left != 0ul )
			{
				memcpy (p_frame + toCopy, (void*)gs_uc_rx_buffer, left);
			}
		}
	}
	#else /* ipconfigZERO_COPY_RX_DRIVER */
	{
		if( p_frame != NULL )
		{
			/* Return a pointer to the earlier DMA buffer. */
			*( pp_recv_frame ) = ( uint8_t * )
				( ( ( gs_rx_desc[nextIdx].addr.val ) & ~( 0x03ul ) ) + 2 );
			/* Set the new DMA-buffer. */
			gs_rx_desc[nextIdx].addr.bm.addr_dw = ( ( uint32_t )p_frame ) / 4;
		}
		else
		{
			/* The driver couldn't not allocate a buffer to receive a packet.
			Leave the current DMA buffer in place. */
		}
	}
	#endif	/* ipconfigZERO_COPY_RX_DRIVER */

	do
	{
		pxHead = &gs_rx_desc[nextIdx];
		pxHead->addr.val &= ~(GMAC_RXD_OWNERSHIP);
		circ_inc32 (&nextIdx, GMAC_RX_BUFFERS);
	} while ((pxHead->status.val & GMAC_RXD_EOF) == 0);

	p_gmac_dev->ul_rx_idx = nextIdx;

	*p_rcv_size = bytesLeft;

//	#warning Just for debugging
//	NVIC_EnableIRQ( GMAC_IRQn );

	return GMAC_OK;
}

extern void vGMACGenerateChecksum( uint8_t *apBuffer, size_t uxLength );

/**
 * \brief Send ulLength bytes from pcFrom. This copies the buffer to one of the
 * GMAC Tx buffers, and then indicates to the GMAC that the buffer is ready.
 * If lEndOfFrame is true then the data being copied is the end of the frame
 * and the frame can be transmitted.
 *
 * \param p_gmac_dev Pointer to the GMAC device instance.
 * \param p_buffer       Pointer to the data buffer.
 * \param ul_size    Length of the frame.
 *
 * \return Length sent.
 */
uint32_t gmac_dev_write(gmac_device_t* p_gmac_dev, void *p_buffer,
		uint32_t ul_size)
{
	volatile gmac_tx_descriptor_t *p_tx_td;

	Gmac *p_hw = p_gmac_dev->p_hw;


	/* Check parameter */
	if (ul_size > GMAC_TX_UNITSIZE) {
		return GMAC_PARAM;
	}

	/* Pointers to the current transmit descriptor */
	p_tx_td = &gs_tx_desc[p_gmac_dev->l_tx_head];

	/* If no free TxTd, buffer can't be sent, schedule the wakeup callback */
	if ((p_tx_td->status.val & GMAC_TXD_USED) == 0)
	{
		return GMAC_TX_BUSY;
	}

	/* Set up/copy data to transmission buffer */
	if (p_buffer && ul_size) {
		/* Driver manages the ring buffer */
		/* Calculating the checksum here is faster than calculating it from the GMAC buffer
		 * because withing p_buffer, it is well aligned */
		#if( ipconfigZERO_COPY_TX_DRIVER != 0 )
		{
			/* Zero-copy... */
			p_tx_td->addr = ( uint32_t ) p_buffer;
		}
		#else
		{
			/* Or memcopy... */
			memcpy((void *)p_tx_td->addr, p_buffer, ul_size);
		}
		#endif /* ipconfigZERO_COPY_TX_DRIVER */
		vGMACGenerateChecksum( ( uint8_t * ) p_tx_td->addr, ( size_t ) ul_size );
	}

	//#warning Trying out
	gmac_start_transmission(p_hw);

	/* Update transmit descriptor status */

	/* The buffer size defined is the length of ethernet frame,
	   so it's always the last buffer of the frame. */
	if( p_gmac_dev->l_tx_head == ( int32_t )( GMAC_TX_BUFFERS - 1 ) )
	{
		/* No need to 'and' with GMAC_TXD_LEN_MASK because ul_size has been checked
		GMAC_TXD_USED will now be cleared. */
		p_tx_td->status.val =
			ul_size | GMAC_TXD_LAST | GMAC_TXD_WRAP;
	} else {
		/* GMAC_TXD_USED will now be cleared. */
		p_tx_td->status.val =
			ul_size | GMAC_TXD_LAST;
	}

	circ_inc32( &p_gmac_dev->l_tx_head, GMAC_TX_BUFFERS );

	/* Now start to transmit if it is still not done */
	gmac_start_transmission(p_hw);

	return GMAC_OK;
}

/**
 * \brief Get current load of transmit.
 *
 * \param p_gmac_dev Pointer to the GMAC device instance.
 *
 * \return Current load of transmit.
 */
uint32_t gmac_dev_get_tx_load(gmac_device_t* p_gmac_dev)
{
	uint16_t us_head = p_gmac_dev->l_tx_head;
	uint16_t us_tail = p_gmac_dev->l_tx_tail;
	return CIRC_CNT(us_head, us_tail, GMAC_TX_BUFFERS);
}

/**
 *  \brief Register/Clear TX wakeup callback.
 *
 * When gmac_dev_write() returns GMAC_TX_BUSY (all transmit descriptor busy), the application
 * task calls gmac_dev_set_tx_wakeup_callback() to register func_wakeup() callback and
 * enters suspend state. The callback is in charge to resume the task once
 * several transmit descriptors have been released. The next time gmac_dev_write() will be called,
 * it shall be successful.
 *
 * This function is usually invoked with NULL callback from the TX wakeup
 * callback itself, to unregister. Once the callback has resumed the
 * application task, there is no need to invoke the callback again.
 *
 * \param p_gmac_dev   Pointer to GMAC device instance.
 * \param func_wakeup    Pointer to wakeup callback function.
 * \param uc_threshold Number of free transmit descriptor before wakeup callback invoked.
 *
 * \return GMAC_OK, GMAC_PARAM on parameter error.
 */
#if( GMAC_USES_WAKEUP_CALLBACK )
uint8_t gmac_dev_set_tx_wakeup_callback(gmac_device_t* p_gmac_dev,
		gmac_dev_wakeup_cb_t func_wakeup_cb, uint8_t uc_threshold)
{
	if (func_wakeup_cb == NULL) {
		p_gmac_dev->func_wakeup_cb = NULL;
	} else {
		if (uc_threshold <= GMAC_TX_BUFFERS) {
			p_gmac_dev->func_wakeup_cb = func_wakeup_cb;
			p_gmac_dev->ul_wakeup_threshold = ( uint32_t )uc_threshold;
		} else {
			return GMAC_PARAM;
		}
	}

	return GMAC_OK;
}
#endif /* GMAC_USES_WAKEUP_CALLBACK */

/**
 * \brief Reset TX & RX queue & statistics.
 *
 * \param p_gmac_dev   Pointer to GMAC device instance.
 */
void gmac_dev_reset(gmac_device_t* p_gmac_dev)
{
	Gmac *p_hw = p_gmac_dev->p_hw;

	gmac_reset_rx_mem(p_gmac_dev);
	gmac_reset_tx_mem(p_gmac_dev);
	gmac_network_control(p_hw, GMAC_NCR_TXEN | GMAC_NCR_RXEN
			| GMAC_NCR_WESTAT | GMAC_NCR_CLRSTAT);
}

void gmac_dev_halt(Gmac* p_gmac);

void gmac_dev_halt(Gmac* p_gmac)
{
	gmac_network_control(p_gmac, GMAC_NCR_WESTAT | GMAC_NCR_CLRSTAT);
	gmac_disable_interrupt(p_gmac, ~0u);
}


/**
 * \brief GMAC Interrupt handler.
 *
 * \param p_gmac_dev   Pointer to GMAC device instance.
 */

#if( GMAC_STATS != 0 )
	extern int logPrintf( const char *pcFormat, ... );

	void gmac_show_irq_counts ()
	{
		int index;
		for (index = 0; index < ARRAY_SIZE(intPairs); index++) {
			if (gmacStats.intStatus[intPairs[index].index]) {
				logPrintf("%s : %6u\n", intPairs[index].name, gmacStats.intStatus[intPairs[index].index]);
			}
		}
	}
#endif

void gmac_handler(gmac_device_t* p_gmac_dev)
{
	Gmac *p_hw = p_gmac_dev->p_hw;

	gmac_tx_descriptor_t *p_tx_td;
	uint32_t ul_tx_status_flag;
#if( GMAC_STATS != 0 )
	int index;
#endif

	uint32_t ul_isr = gmac_get_interrupt_status(p_hw);
	uint32_t ul_rsr = gmac_get_rx_status(p_hw);
	uint32_t ul_tsr = gmac_get_tx_status(p_hw);

	#if( GMAC_STATS != 0 )
	{
		for (index = 0; index < ARRAY_SIZE(intPairs); index++) {
			if (ul_isr & intPairs[index].mask)
				gmacStats.intStatus[intPairs[index].index]++;
		}
	}
	#endif /* GMAC_STATS != 0 */

	/* RX packet */
	if ((ul_isr & GMAC_ISR_RCOMP) || (ul_rsr & (GMAC_RSR_REC|GMAC_RSR_RXOVR|GMAC_RSR_BNA))) {
		/* Clear status */
		gmac_clear_rx_status(p_hw, ul_rsr);

		if (ul_isr & GMAC_ISR_RCOMP)
			ul_rsr |= GMAC_RSR_REC;
		/* Invoke callbacks which can be useful to wake op a task */
		xRxCallback( ul_rsr );
	}

	/* TX packet */
	if ((ul_isr & GMAC_ISR_TCOMP) || (ul_tsr & (GMAC_TSR_TXCOMP|GMAC_TSR_COL|GMAC_TSR_RLE|GMAC_TSR_UND))) {

		ul_tx_status_flag = GMAC_TSR_TXCOMP;
		/* A frame transmitted */

		/* Check RLE */
		if (ul_tsr & GMAC_TSR_RLE) {
			/* Status RLE & Number of discarded buffers */
			ul_tx_status_flag = GMAC_TSR_RLE | CIRC_CNT(p_gmac_dev->l_tx_head,
					p_gmac_dev->l_tx_tail, GMAC_TX_BUFFERS);
			gmac_reset_tx_mem(p_gmac_dev);
			gmac_enable_transmit(p_hw, 1);
		}
		/* Clear status */
		gmac_clear_tx_status(p_hw, ul_tsr);

		if (!CIRC_EMPTY(p_gmac_dev->l_tx_head, p_gmac_dev->l_tx_tail)) {
			/* Check the buffers */
			do {
				p_tx_td = &gs_tx_desc[p_gmac_dev->l_tx_tail];
				/* Any error? Exit if buffer has not been sent yet */
				if ((p_tx_td->status.val & GMAC_TXD_USED) == 0) {
					break;
				}

				/* Notify upper layer that a packet has been sent */
				xTxCallback(ul_tx_status_flag, (void*)p_tx_td->addr); // Function call prvTxCallback
				#if( ipconfigZERO_COPY_TX_DRIVER != 0 )
				{
					p_tx_td->addr = 0ul;
				}
				#endif /* ipconfigZERO_COPY_TX_DRIVER */

				circ_inc32(&p_gmac_dev->l_tx_tail, GMAC_TX_BUFFERS);
			} while (CIRC_CNT(p_gmac_dev->l_tx_head, p_gmac_dev->l_tx_tail,
							GMAC_TX_BUFFERS));
		}

		if (ul_tsr & GMAC_TSR_RLE) {
			/* Notify upper layer RLE */
			xTxCallback(ul_tx_status_flag, NULL);
		}

#if( GMAC_USES_WAKEUP_CALLBACK )
		/* If a wakeup has been scheduled, notify upper layer that it can
		   send other packets, and the sending will be successful. */
		if ((CIRC_SPACE(p_gmac_dev->l_tx_head, p_gmac_dev->l_tx_tail,
				GMAC_TX_BUFFERS) >= p_gmac_dev->ul_wakeup_threshold)
				&& p_gmac_dev->func_wakeup_cb) {
			p_gmac_dev->func_wakeup_cb();
		}
#endif
	}
}

//@}

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
}
#endif
/**INDENT-ON**/
/// @endcond
