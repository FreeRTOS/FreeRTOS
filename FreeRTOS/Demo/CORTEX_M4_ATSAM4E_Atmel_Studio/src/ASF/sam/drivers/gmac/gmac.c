 /**
 * \file
 *
 * \brief GMAC (Ethernet MAC) driver for SAM.
 *
 * Copyright (c) 2013 Atmel Corporation. All rights reserved.
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
 
#include  "compiler.h"
#include "gmac.h"
#include <string.h>
#include "conf_eth.h"

/// @cond 0
/**INDENT-OFF**/
#ifdef __cplusplus
extern "C" {
#endif
/**INDENT-ON**/
/// @endcond

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

/** TX descriptor lists */
COMPILER_ALIGNED(8)
static gmac_tx_descriptor_t gs_tx_desc[GMAC_TX_BUFFERS];
/** TX callback lists */
static gmac_dev_tx_cb_t gs_tx_callback[GMAC_TX_BUFFERS];
/** RX descriptors lists */
COMPILER_ALIGNED(8)
static gmac_rx_descriptor_t gs_rx_desc[GMAC_RX_BUFFERS];
/** Send Buffer. Section 3.6 of AMBA 2.0 spec states that burst should not cross the
 * 1K Boundaries. Receive buffer manager write operations are burst of 2 words => 3 lsb bits
 * of the address shall be set to 0.
 */
COMPILER_ALIGNED(8)
static uint8_t gs_uc_tx_buffer[GMAC_TX_BUFFERS * GMAC_TX_UNITSIZE];

/** Receive Buffer */
COMPILER_ALIGNED(8)
static uint8_t gs_uc_rx_buffer[GMAC_RX_BUFFERS * GMAC_RX_UNITSIZE];

/**
 * GMAC device memory management struct.
 */
typedef struct gmac_dev_mem {
	/* Pointer to allocated buffer for RX. The address should be 8-byte aligned
	and the size should be GMAC_RX_UNITSIZE * wRxSize. */
	uint8_t *p_rx_buffer;
	/* Pointer to allocated RX descriptor list. */
	gmac_rx_descriptor_t *p_rx_dscr;
	/* RX size, in number of registered units (RX descriptors). */
	uint16_t us_rx_size;
	/* Pointer to allocated buffer for TX. The address should be 8-byte aligned
	and the size should be GMAC_TX_UNITSIZE * wTxSize. */
	uint8_t *p_tx_buffer;
	/* Pointer to allocated TX descriptor list. */
	gmac_tx_descriptor_t *p_tx_dscr;
	/* TX size, in number of registered units (TX descriptors). */
	uint16_t us_tx_size;
} gmac_dev_mem_t;

/** Return count in buffer */
#define CIRC_CNT(head,tail,size) (((head) - (tail)) % (size))

/*
 * Return space available, from 0 to size-1.
 * Always leave one free char as a completely full buffer that has (head == tail), 
 * which is the same as empty.
 */
#define CIRC_SPACE(head,tail,size) CIRC_CNT((tail),((head)+1),(size))

/** Circular buffer is empty ? */
#define CIRC_EMPTY(head, tail)     (head == tail)
/** Clear circular buffer */
#define CIRC_CLEAR(head, tail)     (head = tail = 0)

/** Increment head or tail */
static void circ_inc(uint16_t *headortail, uint32_t size)
{
        (*headortail)++;
        if((*headortail) >= size) {
            (*headortail) = 0;
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
static uint8_t gmac_wait_phy(Gmac* p_gmac, const uint32_t ul_retry)
{
	volatile uint32_t ul_retry_count = 0;

	while (!gmac_is_phy_idle(p_gmac)) {
		if (ul_retry == 0) {
			continue;
		}

		ul_retry_count++;

		if (ul_retry_count >= ul_retry) {
			return GMAC_TIMEOUT;
		}
	}
	return GMAC_OK;
}

/**
 * \brief Disable transfer, reset registers and descriptor lists.
 *
 * \param p_dev Pointer to GMAC driver instance.
 *
 */
static void gmac_reset_tx_mem(gmac_device_t* p_dev)
{
	Gmac *p_hw = p_dev->p_hw;
	uint8_t *p_tx_buff = p_dev->p_tx_buffer;
	gmac_tx_descriptor_t *p_td = p_dev->p_tx_dscr;

	uint32_t ul_index;
	uint32_t ul_address;

	/* Disable TX */
	gmac_enable_transmit(p_hw, 0);

	/* Set up the TX descriptors */
	CIRC_CLEAR(p_dev->us_tx_head, p_dev->us_tx_tail);
	for (ul_index = 0; ul_index < p_dev->us_tx_list_size; ul_index++) {
		ul_address = (uint32_t) (&(p_tx_buff[ul_index * GMAC_TX_UNITSIZE]));
		p_td[ul_index].addr = ul_address;
		p_td[ul_index].status.val = GMAC_TXD_USED;
	}
	p_td[p_dev->us_tx_list_size - 1].status.val =
			GMAC_TXD_USED | GMAC_TXD_WRAP;

	/* Set transmit buffer queue */
	gmac_set_tx_queue(p_hw, (uint32_t) p_td);
}

/**
 * \brief Disable receiver, reset registers and descriptor list.
 *
 * \param p_drv Pointer to GMAC Driver instance.
 */
static void gmac_reset_rx_mem(gmac_device_t* p_dev)
{
	Gmac *p_hw = p_dev->p_hw;
	uint8_t *p_rx_buff = p_dev->p_rx_buffer;
	gmac_rx_descriptor_t *pRd = p_dev->p_rx_dscr;

	uint32_t ul_index;
	uint32_t ul_address;

	/* Disable RX */
	gmac_enable_receive(p_hw, 0);

	/* Set up the RX descriptors */
	p_dev->us_rx_idx = 0;
	for (ul_index = 0; ul_index < p_dev->us_rx_list_size; ul_index++) {
		ul_address = (uint32_t) (&(p_rx_buff[ul_index * GMAC_RX_UNITSIZE]));
		pRd[ul_index].addr.val = ul_address & GMAC_RXD_ADDR_MASK;
		pRd[ul_index].status.val = 0;
	}
	pRd[p_dev->us_rx_list_size - 1].addr.val |= GMAC_RXD_WRAP;

	/* Set receive buffer queue */
	gmac_set_rx_queue(p_hw, (uint32_t) pRd);
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
 * \param p_tx_cb Pointer to allocated TX callback list.
 *
 * \return GMAC_OK or GMAC_PARAM.
 */
static uint8_t gmac_init_mem(Gmac* p_gmac, gmac_device_t* p_gmac_dev,
		gmac_dev_mem_t* p_dev_mm,
		gmac_dev_tx_cb_t* p_tx_cb)
{
	if (p_dev_mm->us_rx_size <= 1 || p_dev_mm->us_tx_size <= 1 || p_tx_cb == NULL) {
		return GMAC_PARAM;
	}

	/* Assign RX buffers */
	if (((uint32_t) p_dev_mm->p_rx_buffer & 0x7)
			|| ((uint32_t) p_dev_mm->p_rx_dscr & 0x7)) {
		p_dev_mm->us_rx_size--;
	}
	p_gmac_dev->p_rx_buffer =
			(uint8_t *) ((uint32_t) p_dev_mm->p_rx_buffer & 0xFFFFFFF8);
	p_gmac_dev->p_rx_dscr =
			(gmac_rx_descriptor_t *) ((uint32_t) p_dev_mm->p_rx_dscr 
			& 0xFFFFFFF8);
	p_gmac_dev->us_rx_list_size = p_dev_mm->us_rx_size;

	/* Assign TX buffers */
	if (((uint32_t) p_dev_mm->p_tx_buffer & 0x7)
			|| ((uint32_t) p_dev_mm->p_tx_dscr & 0x7)) {
		p_dev_mm->us_tx_size--;
	}
	p_gmac_dev->p_tx_buffer =
			(uint8_t *) ((uint32_t) p_dev_mm->p_tx_buffer & 0xFFFFFFF8);
	p_gmac_dev->p_tx_dscr =
			(gmac_tx_descriptor_t *) ((uint32_t) p_dev_mm->p_tx_dscr 
			& 0xFFFFFFF8);
	p_gmac_dev->us_tx_list_size = p_dev_mm->us_tx_size;
	p_gmac_dev->func_tx_cb_list = p_tx_cb;

	/* Reset TX & RX */
	gmac_reset_rx_mem(p_gmac_dev);
	gmac_reset_tx_mem(p_gmac_dev);

	/* Enable Rx and Tx, plus the statistics register */
	gmac_enable_transmit(p_gmac, true);
	gmac_enable_receive(p_gmac, true);
	gmac_enable_statistics_write(p_gmac, true);

	/* Set up the interrupts for transmission and errors */
	gmac_enable_interrupt(p_gmac, 
			GMAC_IER_RXUBR | /* Enable receive used bit read interrupt. */
			GMAC_IER_TUR  | /* Enable transmit underrun interrupt. */
			GMAC_IER_RLEX   | /* Enable retry limit  exceeded interrupt. */
			GMAC_IER_TFC | /* Enable transmit buffers exhausted in mid-frame interrupt. */
			GMAC_IER_TCOMP | /* Enable transmit complete interrupt. */
			GMAC_IER_ROVR  | /* Enable receive overrun interrupt. */
			GMAC_IER_HRESP | /* Enable Hresp not OK interrupt. */
			GMAC_IER_PFNZ   | /* Enable pause frame received interrupt. */
			GMAC_IER_PTZ);   /* Enable pause time zero interrupt. */

	return GMAC_OK;
}

/**
 * \brief Read the PHY register.
 *
 * \param p_gmac   Pointer to the GMAC instance. 
 * \param uc_phy_address PHY address.
 * \param uc_address Register address.
 * \param p_value Pointer to a 32-bit location to store read data.
 *
 * \Return GMAC_OK if successfully, GMAC_TIMEOUT if timeout.
 */
uint8_t gmac_phy_read(Gmac* p_gmac, uint8_t uc_phy_address, uint8_t uc_address,
		uint32_t* p_value)
{
	gmac_maintain_phy(p_gmac, uc_phy_address, uc_address, 1, 0);

	if (gmac_wait_phy(p_gmac, MAC_PHY_RETRY_MAX) == GMAC_TIMEOUT) {
		return GMAC_TIMEOUT;
	}
	*p_value = gmac_get_phy_data(p_gmac);
	return GMAC_OK;
}

/**
 * \brief Write the PHY register.
 *
 * \param p_gmac   Pointer to the GMAC instance. 
 * \param uc_phy_address PHY Address.
 * \param uc_address Register Address.
 * \param ul_value Data to write, actually 16-bit data.
 *
 * \Return GMAC_OK if successfully, GMAC_TIMEOUT if timeout.
 */
uint8_t gmac_phy_write(Gmac* p_gmac, uint8_t uc_phy_address,
		uint8_t uc_address, uint32_t ul_value)
{
	gmac_maintain_phy(p_gmac, uc_phy_address, uc_address, 0, ul_value);

	if (gmac_wait_phy(p_gmac, MAC_PHY_RETRY_MAX) == GMAC_TIMEOUT) {
		return GMAC_TIMEOUT;
	}
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
	gmac_dev_mem_t gmac_dev_mm;

	/* Disable TX & RX and more */
	gmac_network_control(p_gmac, 0);
	gmac_disable_interrupt(p_gmac, ~0u);


	gmac_clear_statistics(p_gmac);

	/* Clear all status bits in the receive status register. */
	gmac_clear_rx_status(p_gmac, GMAC_RSR_RXOVR | GMAC_RSR_REC | GMAC_RSR_BNA);

	/* Clear all status bits in the transmit status register */
	gmac_clear_tx_status(p_gmac, GMAC_TSR_UBR | GMAC_TSR_COL | GMAC_TSR_RLE
			| GMAC_TSR_TFC | GMAC_TSR_TXCOMP | GMAC_TSR_UND);

	/* Clear interrupts */
	gmac_get_interrupt_status(p_gmac);

	/* Enable the copy of data into the buffers
	   ignore broadcasts, and not copy FCS. */
	gmac_set_configure(p_gmac,
			gmac_get_configure(p_gmac) | GMAC_NCFGR_IRXFCS| GMAC_NCFGR_PEN);

	gmac_enable_copy_all(p_gmac, p_opt->uc_copy_all_frame);
	gmac_disable_broadcast(p_gmac, p_opt->uc_no_boardcast);

	/* Fill in GMAC device memory management */
	gmac_dev_mm.p_rx_buffer = gs_uc_rx_buffer;
	gmac_dev_mm.p_rx_dscr = gs_rx_desc;
	gmac_dev_mm.us_rx_size = GMAC_RX_BUFFERS;

	gmac_dev_mm.p_tx_buffer = gs_uc_tx_buffer;
	gmac_dev_mm.p_tx_dscr = gs_tx_desc;
	gmac_dev_mm.us_tx_size = GMAC_TX_BUFFERS;

	gmac_init_mem(p_gmac, p_gmac_dev, &gmac_dev_mm, gs_tx_callback);

	gmac_set_address(p_gmac, 0, p_opt->uc_mac_addr);

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
		uint32_t ul_frame_size, uint32_t* p_rcv_size)
{
	uint16_t us_buffer_length;
	uint32_t tmp_ul_frame_size = 0;
	uint8_t *p_tmp_frame = 0;
	uint16_t us_tmp_idx = p_gmac_dev->us_rx_idx;
	gmac_rx_descriptor_t *p_rx_td =
			&p_gmac_dev->p_rx_dscr[p_gmac_dev->us_rx_idx];
	int8_t c_is_frame = 0;

	if (p_frame == NULL)
		return GMAC_PARAM;

	/* Set the default return value */
	*p_rcv_size = 0;

	/* Process received RX descriptor */
	while ((p_rx_td->addr.val & GMAC_RXD_OWNERSHIP) == GMAC_RXD_OWNERSHIP) {
		/* A start of frame has been received, discard previous fragments */
		if ((p_rx_td->status.val & GMAC_RXD_SOF) == GMAC_RXD_SOF) {
			/* Skip previous fragment */
			while (us_tmp_idx != p_gmac_dev->us_rx_idx) {
				p_rx_td = &p_gmac_dev->p_rx_dscr[p_gmac_dev->us_rx_idx];
				p_rx_td->addr.val &= ~(GMAC_RXD_OWNERSHIP);

				circ_inc(&p_gmac_dev->us_rx_idx, p_gmac_dev->us_rx_list_size);
			}
			/* Reset the temporary frame pointer */
			p_tmp_frame = p_frame;
			tmp_ul_frame_size = 0;
			/* Start to gather buffers in a frame */
			c_is_frame = 1;
		}

		/* Increment the pointer */
		circ_inc(&us_tmp_idx, p_gmac_dev->us_rx_list_size);

		/* Copy data in the frame buffer */
		if (c_is_frame) {
			if (us_tmp_idx == p_gmac_dev->us_rx_idx) {
				do {
					p_rx_td = &p_gmac_dev->p_rx_dscr[p_gmac_dev->us_rx_idx];
					p_rx_td->addr.val &= ~(GMAC_RXD_OWNERSHIP);
					circ_inc(&p_gmac_dev->us_rx_idx, p_gmac_dev->us_rx_list_size);
							
				} while (us_tmp_idx != p_gmac_dev->us_rx_idx);

				return GMAC_RX_NULL;
			}
			/* Copy the buffer into the application frame */
			us_buffer_length = GMAC_RX_UNITSIZE;
			if ((tmp_ul_frame_size + us_buffer_length) > ul_frame_size) {
				us_buffer_length = ul_frame_size - tmp_ul_frame_size;
			}

			memcpy(p_tmp_frame,
					(void *)(p_rx_td->addr.val & GMAC_RXD_ADDR_MASK),
					us_buffer_length);
			p_tmp_frame += us_buffer_length;
			tmp_ul_frame_size += us_buffer_length;

			/* An end of frame has been received, return the data */
			if ((p_rx_td->status.val & GMAC_RXD_EOF) == GMAC_RXD_EOF) {
				/* Frame size from the GMAC */
				*p_rcv_size = (p_rx_td->status.val & GMAC_RXD_LEN_MASK);

				/* All data have been copied in the application frame buffer => release TD */
				while (p_gmac_dev->us_rx_idx != us_tmp_idx) {
					p_rx_td = &p_gmac_dev->p_rx_dscr[p_gmac_dev->us_rx_idx];
					p_rx_td->addr.val &= ~(GMAC_RXD_OWNERSHIP);
					circ_inc(&p_gmac_dev->us_rx_idx, p_gmac_dev->us_rx_list_size);
				}

				/* Application frame buffer is too small so that all data have not been copied */
				if (tmp_ul_frame_size < *p_rcv_size) {
					return GMAC_SIZE_TOO_SMALL;
				}

				return GMAC_OK;
			}
		}
		/* SOF has not been detected, skip the fragment */
		else {
			p_rx_td->addr.val &= ~(GMAC_RXD_OWNERSHIP);
			p_gmac_dev->us_rx_idx = us_tmp_idx;
		}

		/* Process the next buffer */
		p_rx_td = &p_gmac_dev->p_rx_dscr[us_tmp_idx];
	}

	return GMAC_RX_NULL;
}

/**
 * \brief Send ulLength bytes from pcFrom. This copies the buffer to one of the
 * GMAC Tx buffers, and then indicates to the GMAC that the buffer is ready.
 * If lEndOfFrame is true then the data being copied is the end of the frame
 * and the frame can be transmitted.
 *
 * \param p_gmac_dev Pointer to the GMAC device instance.
 * \param p_buffer       Pointer to the data buffer.
 * \param ul_size    Length of the frame.
 * \param func_tx_cb  Transmit callback function.
 *
 * \return Length sent.
 */
uint32_t gmac_dev_write(gmac_device_t* p_gmac_dev, void *p_buffer,
		uint32_t ul_size, gmac_dev_tx_cb_t func_tx_cb)
{

	volatile gmac_tx_descriptor_t *p_tx_td;
	volatile gmac_dev_tx_cb_t *p_func_tx_cb;

	Gmac *p_hw = p_gmac_dev->p_hw;


	/* Check parameter */
	if (ul_size > GMAC_TX_UNITSIZE) {
		return GMAC_PARAM;
	}

	/* Pointers to the current transmit descriptor */
	p_tx_td = &p_gmac_dev->p_tx_dscr[p_gmac_dev->us_tx_head];

	/* If no free TxTd, buffer can't be sent, schedule the wakeup callback */
	if (CIRC_SPACE(p_gmac_dev->us_tx_head, p_gmac_dev->us_tx_tail,
					p_gmac_dev->us_tx_list_size) == 0) {
		if (p_tx_td[p_gmac_dev->us_tx_head].status.val & GMAC_TXD_USED)
			return GMAC_TX_BUSY;
	}

	/* Pointers to the current Tx callback */
	p_func_tx_cb = &p_gmac_dev->func_tx_cb_list[p_gmac_dev->us_tx_head];

	/* Set up/copy data to transmission buffer */
	if (p_buffer && ul_size) {
		/* Driver manages the ring buffer */
		memcpy((void *)p_tx_td->addr, p_buffer, ul_size);
	}

	/* Tx callback */
	*p_func_tx_cb = func_tx_cb;

	/* Update transmit descriptor status */

	/* The buffer size defined is the length of ethernet frame,
	   so it's always the last buffer of the frame. */
	if (p_gmac_dev->us_tx_head == p_gmac_dev->us_tx_list_size - 1) {
		p_tx_td->status.val =
				(ul_size & GMAC_TXD_LEN_MASK) | GMAC_TXD_LAST
				| GMAC_TXD_WRAP;
	} else {
		p_tx_td->status.val =
				(ul_size & GMAC_TXD_LEN_MASK) | GMAC_TXD_LAST;
	}

	circ_inc(&p_gmac_dev->us_tx_head, p_gmac_dev->us_tx_list_size);

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
	uint16_t us_head = p_gmac_dev->us_tx_head;
	uint16_t us_tail = p_gmac_dev->us_tx_tail;
	return CIRC_CNT(us_head, us_tail, p_gmac_dev->us_tx_list_size);
}

/**
 * \brief Register/Clear RX callback. Callback will be invoked after the next received
 * frame.
 *
 * When gmac_dev_read() returns GMAC_RX_NULL, the application task calls
 * gmac_dev_set_rx_callback() to register func_rx_cb() callback and enters suspend state.
 * The callback is in charge to resume the task once a new frame has been
 * received. The next time gmac_dev_read() is called, it will be successful.
 *
 * This function is usually invoked from the RX callback itself with NULL
 * callback, to unregister. Once the callback has resumed the application task,
 * there is no need to invoke the callback again.
 *
 * \param p_gmac_dev Pointer to the GMAC device instance.
 * \param func_tx_cb  Receive callback function.
 */
void gmac_dev_set_rx_callback(gmac_device_t* p_gmac_dev,
		gmac_dev_tx_cb_t func_rx_cb)
{
	Gmac *p_hw = p_gmac_dev->p_hw;

	if (func_rx_cb == NULL) {
		gmac_disable_interrupt(p_hw, GMAC_IDR_RCOMP);
		p_gmac_dev->func_rx_cb = NULL;
	} else {
		p_gmac_dev->func_rx_cb = func_rx_cb;
		gmac_enable_interrupt(p_hw, GMAC_IER_RCOMP);
	}
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
uint8_t gmac_dev_set_tx_wakeup_callback(gmac_device_t* p_gmac_dev,
		gmac_dev_wakeup_cb_t func_wakeup_cb, uint8_t uc_threshold)
{
	if (func_wakeup_cb == NULL) {
		p_gmac_dev->func_wakeup_cb = NULL;
	} else {
		if (uc_threshold <= p_gmac_dev->us_tx_list_size) {
			p_gmac_dev->func_wakeup_cb = func_wakeup_cb;
			p_gmac_dev->uc_wakeup_threshold = uc_threshold;
		} else {
			return GMAC_PARAM;
		}
	}

	return GMAC_OK;
}


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


/**
 * \brief GMAC Interrupt handler.
 *
 * \param p_gmac_dev   Pointer to GMAC device instance.
 */
void gmac_handler(gmac_device_t* p_gmac_dev)
{
	Gmac *p_hw = p_gmac_dev->p_hw;

	gmac_tx_descriptor_t *p_tx_td;
	gmac_dev_tx_cb_t *p_tx_cb;
	volatile uint32_t ul_isr;
	volatile uint32_t ul_rsr;
	volatile uint32_t ul_tsr;
	uint32_t ul_rx_status_flag;
	uint32_t ul_tx_status_flag;

	ul_isr = gmac_get_interrupt_status(p_hw);
	ul_rsr = gmac_get_rx_status(p_hw);
	ul_tsr = gmac_get_tx_status(p_hw);

	ul_isr &= ~(gmac_get_interrupt_mask(p_hw) | 0xF8030300);

	/* RX packet */
	if ((ul_isr & GMAC_ISR_RCOMP) || (ul_rsr & GMAC_RSR_REC)) {
		ul_rx_status_flag = GMAC_RSR_REC;

		/* Check OVR */
		if (ul_rsr & GMAC_RSR_RXOVR) {
			ul_rx_status_flag |= GMAC_RSR_RXOVR;
		}
		/* Check BNA */
		if (ul_rsr & GMAC_RSR_BNA) {
			ul_rx_status_flag |= GMAC_RSR_BNA;
		}
		/* Clear status */
		gmac_clear_rx_status(p_hw, ul_rx_status_flag);

		/* Invoke callbacks */
		if (p_gmac_dev->func_rx_cb) {
			p_gmac_dev->func_rx_cb(ul_rx_status_flag);
		}
	}

	/* TX packet */
	if ((ul_isr & GMAC_ISR_TCOMP) || (ul_tsr & GMAC_TSR_TXCOMP)) {

		ul_tx_status_flag = GMAC_TSR_TXCOMP;

		/* A frame transmitted */

		/* Check RLE */
		if (ul_tsr & GMAC_TSR_RLE) {
			/* Status RLE & Number of discarded buffers */
			ul_tx_status_flag = GMAC_TSR_RLE | CIRC_CNT(p_gmac_dev->us_tx_head,
					p_gmac_dev->us_tx_tail, p_gmac_dev->us_tx_list_size);
			p_tx_cb = &p_gmac_dev->func_tx_cb_list[p_gmac_dev->us_tx_tail];
			gmac_reset_tx_mem(p_gmac_dev);
			gmac_enable_transmit(p_hw, 1);
		}
		/* Check COL */
		if (ul_tsr & GMAC_TSR_COL) {
			ul_tx_status_flag |= GMAC_TSR_COL;
		}
		/* Check UND */
		if (ul_tsr & GMAC_TSR_UND) {
			ul_tx_status_flag |= GMAC_TSR_UND;
		}
		/* Clear status */
		gmac_clear_tx_status(p_hw, ul_tx_status_flag);

		if (!CIRC_EMPTY(p_gmac_dev->us_tx_head, p_gmac_dev->us_tx_tail)) {
			/* Check the buffers */
			do {
				p_tx_td = &p_gmac_dev->p_tx_dscr[p_gmac_dev->us_tx_tail];
				p_tx_cb = &p_gmac_dev->func_tx_cb_list[p_gmac_dev->us_tx_tail];
				/* Any error? Exit if buffer has not been sent yet */
				if ((p_tx_td->status.val & GMAC_TXD_USED) == 0) {
					break;
				}

				/* Notify upper layer that a packet has been sent */
				if (*p_tx_cb) {
					(*p_tx_cb) (ul_tx_status_flag);
				}

				circ_inc(&p_gmac_dev->us_tx_tail, p_gmac_dev->us_tx_list_size);
			} while (CIRC_CNT(p_gmac_dev->us_tx_head, p_gmac_dev->us_tx_tail,
							p_gmac_dev->us_tx_list_size));
		}

		if (ul_tsr & GMAC_TSR_RLE) {
			/* Notify upper layer RLE */
			if (*p_tx_cb) {
				(*p_tx_cb) (ul_tx_status_flag);
			}
		}

		/* If a wakeup has been scheduled, notify upper layer that it can
		   send other packets, and the sending will be successful. */
		if ((CIRC_SPACE(p_gmac_dev->us_tx_head, p_gmac_dev->us_tx_tail,
				p_gmac_dev->us_tx_list_size) >= p_gmac_dev->uc_wakeup_threshold)
				&& p_gmac_dev->func_wakeup_cb) {
			p_gmac_dev->func_wakeup_cb();
		}
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
