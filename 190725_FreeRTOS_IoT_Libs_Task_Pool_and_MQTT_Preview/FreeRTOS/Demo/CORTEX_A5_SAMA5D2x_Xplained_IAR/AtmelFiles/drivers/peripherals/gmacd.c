/* ----------------------------------------------------------------------------
 *         SAM Software Package License
 * ----------------------------------------------------------------------------
 * Copyright (c) 2015, Atmel Corporation
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * - Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the disclaimer below.
 *
 * Atmel's name may not be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * DISCLAIMER: THIS SOFTWARE IS PROVIDED BY ATMEL "AS IS" AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NON-INFRINGEMENT ARE
 * DISCLAIMED. IN NO EVENT SHALL ATMEL BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA,
 * OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF
 * LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * ----------------------------------------------------------------------------
 */

/*---------------------------------------------------------------------------
 *         Headers
 *---------------------------------------------------------------------------*/

#include "chip.h"
#include "trace.h"
#include "ring.h"

#include "peripherals/aic.h"
#include "peripherals/gmacd.h"
#include "peripherals/gmac.h"
#include "peripherals/l2cc.h"
#include "peripherals/pmc.h"

#include <string.h>
#include <assert.h>

//------------------------------------------------------------------------------
//         Definitions
//------------------------------------------------------------------------------

// Interrupt bits
#define GMAC_INT_RX_BITS     (GMAC_IER_RCOMP | GMAC_IER_RXUBR | GMAC_IER_ROVR)
#define GMAC_INT_TX_ERR_BITS (GMAC_IER_TUR | GMAC_IER_RLEX | GMAC_IER_TFC)
#define GMAC_INT_TX_BITS     (GMAC_INT_TX_ERR_BITS | GMAC_IER_TCOMP)

/*---------------------------------------------------------------------------
 *         Types
 *---------------------------------------------------------------------------*/

struct _gmacd_irq_handler {
	Gmac*           addr;
	struct _gmacd** gmacd;
	uint32_t        irq;
	aic_handler_t   handler;
};

/*---------------------------------------------------------------------------
 *         IRQ Handlers
 *---------------------------------------------------------------------------*/

#ifdef CONFIG_HAVE_GMAC_QUEUES
#if GMAC_NUM_QUEUES != 3
#error This driver assumes that GMAC_NUM_QUEUES is 3
#endif
#endif

static struct _gmacd* _gmacd0;
#ifdef GMAC1
static struct _gmacd* _gmacd1;
#endif

static void _gmacd_handler(struct _gmacd* gmacd, uint8_t queue);

static void _gmacd_gmac0_irq_handler(void)
{
	_gmacd_handler(_gmacd0, 0);
}

#ifdef CONFIG_HAVE_GMAC_QUEUES
static void _gmacd_gmac0q1_irq_handler(void)
{
	_gmacd_handler(_gmacd0, 1);
}

static void _gmacd_gmac0q2_irq_handler(void)
{
	_gmacd_handler(_gmacd0, 2);
}
#endif

#ifdef GMAC1
static void _gmacd_gmac1_irq_handler(void)
{
	_gmacd_handler(_gmacd1, 0);
}

#ifdef CONFIG_HAVE_GMAC_QUEUES
static void _gmacd_gmac1q1_irq_handler(void)
{
	_gmacd_handler(_gmacd1, 1);
}

static void _gmacd_gmac1q2_irq_handler(void)
{
	_gmacd_handler(_gmacd1, 2);
}
#endif
#endif

static const struct _gmacd_irq_handler _gmacd_irq_handlers[] = {
	{ GMAC0, &_gmacd0, ID_GMAC0,    _gmacd_gmac0_irq_handler },
#ifdef CONFIG_HAVE_GMAC_QUEUES
	{ GMAC0, &_gmacd0, ID_GMAC0_Q1, _gmacd_gmac0q1_irq_handler },
	{ GMAC0, &_gmacd0, ID_GMAC0_Q2, _gmacd_gmac0q2_irq_handler },
#endif
#ifdef GMAC1
	{ GMAC1, &_gmacd1, ID_GMAC1,    _gmacd_gmac1_irq_handler },
#ifdef CONFIG_HAVE_GMAC_QUEUES
	{ GMAC1, &_gmacd1, ID_GMAC1_Q1, _gmacd_gmac1q1_irq_handler },
	{ GMAC1, &_gmacd1, ID_GMAC1_Q2, _gmacd_gmac1q2_irq_handler },
#endif
#endif
};

/*---------------------------------------------------------------------------
 *         Dummy Buffers for unconfigured queues
 *---------------------------------------------------------------------------*/

#define DUMMY_BUFFERS 2
#define DUMMY_UNITSIZE 128

/** TX descriptors list */
ALIGNED(8) SECTION(".region_ddr_nocache")
static struct _gmac_desc dummy_tx_desc[DUMMY_BUFFERS];

/** RX descriptors list */
ALIGNED(8) SECTION(".region_ddr_nocache")
static struct _gmac_desc dummy_rx_desc[DUMMY_BUFFERS];

/** Send Buffer */
ALIGNED(32)
static uint8_t dummy_buffer[DUMMY_BUFFERS * DUMMY_UNITSIZE];

/*---------------------------------------------------------------------------
 *         Local functions
 *---------------------------------------------------------------------------*/

/**
 *  \brief Disable TX & reset registers and descriptor list
 *  \param gmacd Pointer to GMAC Driver instance.
 */
static void _gmacd_reset_tx(struct _gmacd* gmacd, uint8_t queue)
{
	struct _gmacd_queue* q = &gmacd->queues[queue];
	uint32_t addr = (uint32_t)q->tx_buffer;
	uint32_t i;

	/* Disable TX */
	gmac_transmit_enable(gmacd->gmac, false);

	/* Setup the TX descriptors */
	RING_CLEAR(q->tx_head, q->tx_tail);
	for (i = 0; i < q->tx_size; i++) {
		q->tx_desc[i].addr = addr;
		DSB();
		q->tx_desc[i].status = GMAC_TX_STATUS_USED;
		addr += GMAC_TX_UNITSIZE;
	}
	q->tx_desc[q->tx_size - 1].status |= GMAC_TX_STATUS_WRAP;

	/* Transmit Buffer Queue Pointer Register */
	gmac_set_tx_desc(gmacd->gmac, queue, q->tx_desc);
}

/**
 *  \brief Disable RX & reset registers and descriptor list
 *  \param gmacd Pointer to GMAC Driver instance.
 */
static void _gmacd_reset_rx(struct _gmacd* gmacd, uint8_t queue)
{
	struct _gmacd_queue* q = &gmacd->queues[queue];
	uint32_t addr = (uint32_t)q->rx_buffer;
	uint32_t i;

	/* Disable RX */
	gmac_receive_enable(gmacd->gmac, false);

	/* Setup the RX descriptors */
	q->rx_head = 0;
	for (i = 0; i < q->rx_size; i++) {
		q->rx_desc[i].addr = addr & GMAC_RX_ADDR_MASK;
		DSB();
		q->rx_desc[i].status = 0;
		addr += GMAC_RX_UNITSIZE;
	}
	q->rx_desc[q->rx_size - 1].addr |= GMAC_RX_ADDR_WRAP;

	/* Receive Buffer Queue Pointer Register */
	gmac_set_rx_desc(gmacd->gmac, queue, q->rx_desc);
}

/**
 *  \brief Process successfully sent packets
 *  \param gmacd Pointer to GMAC Driver instance.
 */
static void _gmacd_tx_complete_handler(struct _gmacd* gmacd, uint8_t queue)
{
	Gmac* gmac = gmacd->gmac;
	struct _gmacd_queue* q = &gmacd->queues[queue];
	struct _gmac_desc *desc;
	gmacd_callback_t callback;
	uint32_t tsr;

	//printf("<TX>\r\n");

	/* Clear status */
	tsr = gmac_get_tx_status(gmac);
	gmac_clear_tx_status(gmac, tsr);

	while (!RING_EMPTY(q->tx_head, q->tx_tail)) {
		desc = &q->tx_desc[q->tx_tail];

		/* Exit if frame has not been sent yet:
		 * On TX completion, the GMAC set the USED bit only into the
		 * very first buffer descriptor of the sent frame.
		 * Otherwise it updates this descriptor with status error bits.
		 * This is the descriptor writeback.
		 */
		if ((desc->status & GMAC_TX_STATUS_USED) == 0)
			break;

		/* Process all buffers of the current transmitted frame */
		while ((desc->status & GMAC_TX_STATUS_LASTBUF) == 0) {
			RING_INC(q->tx_tail, q->tx_size);
			desc = &q->tx_desc[q->tx_tail];
		}

		/* Notify upper layer that a frame has been sent */
		if (q->tx_callbacks) {
			callback = q->tx_callbacks[q->tx_tail];
			if (callback)
				callback(queue, tsr);
		}

		/* Go to next frame */
		RING_INC(q->tx_tail, q->tx_size);
	}

	/* If a wakeup callback has been set, notify upper layer that it can
	   send more packets now */
	if (q->tx_wakeup_callback) {
		if (RING_SPACE(q->tx_head, q->tx_tail, q->tx_size) >=
				q->tx_wakeup_threshold) {
			q->tx_wakeup_callback(queue);
		}
	}
}

/**
 *  \brief Reset TX queue when errors are detected
 *  \param gmacd Pointer to GMAC Driver instance.
 */
static void _gmacd_tx_error_handler(struct _gmacd* gmacd, uint8_t queue)
{
	Gmac *gmac = gmacd->gmac;
	struct _gmacd_queue* q = &gmacd->queues[queue];
	struct _gmac_desc* desc;
	gmacd_callback_t callback;
	uint32_t tsr;

	printf("<TXERR>\r\n");

	/* Clear TXEN bit into the Network Configuration Register:
	 * this is a workaround to recover from TX lockups that
	 * occur on sama5d4 gmac (r1p24f2) when using  scatter-gather.
	 * This issue has never been seen on sama5d4 gmac (r1p31).
	 */
	gmac_transmit_enable(gmac, false);

	/* The following step should be optional since this function is called
	 * directly by the IRQ handler. Indeed, according to Cadence
	 * documentation, the transmission is halted on errors such as
	 * too many retries or transmit under run.
	 * However it would become mandatory if the call of this function
	 * were scheduled as a task by the IRQ handler (this is how Linux
	 * driver works). Then this function might compete with GMACD_Send().
	 *
	 * Setting bit 10, tx_halt, of the Network Control Register is not enough:
	 * We should wait for bit 3, tx_go, of the Transmit Status Register to
	 * be cleared at transmit completion if a frame is being transmitted.
	 */
	gmac_halt_transmission(gmac);
	while (gmac_get_tx_status(gmac) & GMAC_TSR_TXGO);

	/* Treat frames in TX queue including the ones that caused the error. */
	while (!RING_EMPTY(q->tx_head, q->tx_tail)) {
		int tx_completed = 0;
		desc = &q->tx_desc[q->tx_tail];

		/* Check USED bit on the very first buffer descriptor to validate
		 * TX completion.
		 */
		if (desc->status & GMAC_TX_STATUS_USED)
			tx_completed = 1;

		/* Go to the last buffer descriptor of the frame */
		while ((desc->status & GMAC_TX_STATUS_LASTBUF) == 0) {
			RING_INC(q->tx_tail, q->tx_size);
			desc = &q->tx_desc[q->tx_tail];
		}

		/* Notify upper layer that a frame status */
		// TODO: which error to notify?
		if (q->tx_callbacks) {
			callback = q->tx_callbacks[q->tx_tail];
			if (callback)
				callback(queue, tx_completed ? GMAC_TSR_TXCOMP : 0);
		}

		/* Go to next frame */
		RING_INC(q->tx_tail, q->tx_size);
	}

	/* Reset TX queue */
	_gmacd_reset_tx(gmacd, queue);

	/* Clear status */
	tsr = gmac_get_tx_status(gmac);
	gmac_clear_tx_status(gmac, tsr);

	/* Now we are ready to start transmission again */
	gmac_transmit_enable(gmac, true);
	if (q->tx_wakeup_callback)
		q->tx_wakeup_callback(queue);
}

/*---------------------------------------------------------------------------
 *         Exported functions
 *---------------------------------------------------------------------------*/

/**
 *  \brief GMAC Interrupt handler
 *  \param gmacd Pointer to GMAC Driver instance.
 */
static void _gmacd_handler(struct _gmacd * gmacd, uint8_t queue)
{
	Gmac *gmac = gmacd->gmac;
	struct _gmacd_queue* q = &gmacd->queues[queue];
	uint32_t isr;
	uint32_t rsr;

	/* Interrupt Status Register is cleared on read */
	while ((isr = gmac_get_it_status(gmac, queue)) != 0) {
		/* RX packet */
		if (isr & GMAC_INT_RX_BITS) {
			/* Clear status */
			rsr = gmac_get_rx_status(gmac);
			gmac_clear_rx_status(gmac, rsr);

			/* Invoke callback */
			if (q->rx_callback)
				q->rx_callback(queue, rsr);
		}

		/* TX error */
		if (isr & GMAC_INT_TX_ERR_BITS) {
			_gmacd_tx_error_handler(gmacd, queue);
			break;
		}

		/* TX packet */
		if (isr & GMAC_IER_TCOMP) {
			_gmacd_tx_complete_handler(gmacd, queue);
		}

		/* HRESP not OK */
		if (isr & GMAC_IER_HRESP) {
			trace_error("HRESP not OK\n\r");
		}
	}
}

/**
 * \brief Initialize the GMAC with the Gmac controller address
 *  \param gmacd Pointer to GMAC Driver instance.
 *  \param gmac    Pointer to HW address for registers.
 *  \param enableCAF    Enable/Disable CopyAllFrame.
 *  \param enableNBC    Enable/Disable NoBroadCast.
 */
void gmacd_configure(struct _gmacd * gmacd,
	   Gmac * gmac, uint8_t enableCAF, uint8_t enableNBC)
{
	uint32_t ncfgr;
	int i;

	/* Initialize struct */
	gmacd->gmac = gmac;

	gmac_configure(gmac);

	uint32_t id = get_gmac_id_from_addr(gmac);
	for (i = 0; i < ARRAY_SIZE(_gmacd_irq_handlers); i++) {
		if (_gmacd_irq_handlers[i].addr == gmac) {
			*_gmacd_irq_handlers[i].gmacd = gmacd;
			aic_set_source_vector(_gmacd_irq_handlers[i].irq,
					_gmacd_irq_handlers[i].handler);
		}
	}
	aic_enable(id);

	/* Enable the copy of data into the buffers
	   ignore broadcasts, and don't copy FCS. */
	ncfgr = gmac_get_network_config_register(gmac);
	ncfgr |= GMAC_NCFGR_FD;
	if (enableCAF) {
		ncfgr |= GMAC_NCFGR_CAF;
	}
	if (enableNBC) {
		ncfgr |= GMAC_NCFGR_NBC;
	}
	gmac_set_network_config_register(gmac, ncfgr);

	for (i = 0; i < GMAC_NUM_QUEUES; i++) {
		gmacd_setup_queue(gmacd, i,
				DUMMY_BUFFERS, dummy_buffer, dummy_rx_desc,
				DUMMY_BUFFERS, dummy_buffer, dummy_tx_desc,
				NULL);
	}
}

/**
 * Initialize necessary allocated buffer lists for GMAC Driver to transfer data.
 * Must be invoked after GMACD_Init() but before RX/TX start.
 * \param gmacd Pointer to GMAC Driver instance.
 * \param rx_buffer Pointer to allocated buffer for RX. The address should
 *                  be 8-byte aligned and the size should be
 *                  GMAC_RX_UNITSIZE * wRxSize.
 * \param rx_desc      Pointer to allocated RX descriptor list.
 * \param wRxSize   RX size, in number of registered units (RX descriptors).
 * \param tx_buffer Pointer to allocated buffer for TX. The address should
 *                  be 8-byte aligned and the size should be
 *                  GMAC_TX_UNITSIZE * wTxSize.
 * \param tx_desc      Pointer to allocated TX descriptor list.
 * \param pTxCb     Pointer to allocated TX callback list.
 * \param wTxSize   TX size, in number of registered units (TX descriptors).
 * \return GMACD_OK or GMACD_PARAM.
 * \note If input address is not 8-byte aligned the address is automatically
 *       adjusted and the list size is reduced by one.
 */


uint8_t gmacd_setup_queue(struct _gmacd* gmacd, uint8_t queue,
		uint16_t rx_size, uint8_t* rx_buffer, struct _gmac_desc* rx_desc,
		uint16_t tx_size, uint8_t* tx_buffer, struct _gmac_desc* tx_desc,
		gmacd_callback_t *tx_callbacks)
{
	Gmac *gmac = gmacd->gmac;
	struct _gmacd_queue* q = &gmacd->queues[queue];

	if (rx_size <= 1 || tx_size <= 1)
		return GMACD_PARAM;

	/* Assign RX buffers */
	if (((uint32_t)rx_buffer & 0x7)
	    || ((uint32_t)rx_desc & 0x7)) {
		rx_size--;
		trace_debug("RX list address adjusted\n\r");
	}
	q->rx_buffer = (uint8_t*)((uint32_t)rx_buffer & 0xFFFFFFF8);
	q->rx_desc = (struct _gmac_desc *)((uint32_t)rx_desc & 0xFFFFFFF8);
	q->rx_size = rx_size;
	q->rx_callback = NULL;

	/* Assign TX buffers */
	if (((uint32_t)tx_buffer & 0x7)
	    || ((uint32_t)tx_desc & 0x7)) {
		tx_size--;
		trace_debug("TX list address adjusted\n\r");
	}
	q->tx_buffer = (uint8_t*)((uint32_t)tx_buffer & 0xFFFFFFF8);
	q->tx_desc = (struct _gmac_desc*)((uint32_t)tx_desc & 0xFFFFFFF8);
	q->tx_size = tx_size;
	q->tx_callbacks = tx_callbacks;
	q->tx_wakeup_callback = NULL;

	/* Reset TX & RX */
	_gmacd_reset_rx(gmacd, queue);
	_gmacd_reset_tx(gmacd, queue);

	/* Setup the interrupts for RX/TX completion (and errors) */
	gmac_enable_it(gmac, queue, GMAC_INT_RX_BITS | GMAC_INT_TX_BITS | GMAC_IER_HRESP);

	return GMACD_OK;
}

void gmacd_start(struct _gmacd * gmacd)
{
	/* Enable Rx and Tx, plus the stats register. */
	gmac_transmit_enable(gmacd->gmac, true);
	gmac_receive_enable(gmacd->gmac, true);
	gmac_enable_statistics_write(gmacd->gmac, true);
}

/**
 * Reset TX & RX queue & statistics
 * \param gmacd Pointer to GMAC Driver instance.
 */
void gmacd_reset(struct _gmacd* gmacd)
{
	int i;
	for (i = 0; i < GMAC_NUM_QUEUES; i++) {
		_gmacd_reset_rx(gmacd, i);
		_gmacd_reset_tx(gmacd, i);
	}

	gmac_set_network_control_register(gmacd->gmac, GMAC_NCR_TXEN | GMAC_NCR_RXEN |
			GMAC_NCR_WESTAT | GMAC_NCR_CLRSTAT);
}

/**
 * \brief Send a frame splitted into buffers. If the frame size is larger than transfer buffer size
 * error returned. If frame transfer status is monitored, specify callback for each frame.
 *  \param gmacd Pointer to GMAC Driver instance.
 *  \param sgl Pointer to a scatter-gather list describing the buffers of the ethernet frame.
 *  \param fTxCb Pointer to callback function.
 */
uint8_t gmacd_send_sg(struct _gmacd* gmacd, uint8_t queue,
		const struct _gmac_sg_list* sgl, gmacd_callback_t callback)
{
	Gmac* gmac = gmacd->gmac;
	struct _gmacd_queue* q = &gmacd->queues[queue];
	struct _gmac_desc* desc;
	uint16_t idx, tx_head;
	int i;

	if (callback && !q->tx_callbacks) {
		trace_error("Cannot set send callback, no tx_callbacks "\
				"buffer configured for queue %u", queue);
	}

	/* Check parameter */
	if (!sgl->size) {
		trace_error("gmacd_send_sg: ethernet frame is empty.\r\n");
		return GMACD_PARAM;
	}
	if (sgl->size >= q->tx_size) {
		trace_error("gmacd_send_sg: ethernet frame has too many buffers.\r\n");
		return GMACD_PARAM;
	}

	/* Check available space */
	if (RING_SPACE(q->tx_head, q->tx_tail, q->tx_size) < sgl->size) {
		trace_error("gmacd_send_sg: not enough free buffers in TX queue.\r\n");
		return GMACD_TX_BUSY;
	}

	/* Tag end of TX queue */
	tx_head = fixed_mod(q->tx_head + sgl->size, q->tx_size);
	idx = tx_head;
	if (q->tx_callbacks)
		q->tx_callbacks[idx] = NULL;
	desc = &q->tx_desc[idx];
	desc->status |= GMAC_TX_STATUS_USED;

	/* Update buffer descriptors in reverse order to avoid a race
	 * condition with hardware.
	 */
	for (i = sgl->size - 1; i >= 0; i--) {
		const struct _gmac_sg *sg = &sgl->entries[i];
		uint32_t status;

		if (sg->size > GMAC_TX_UNITSIZE) {
			trace_error("gmacd_send_sg: buffer size is too big.\r\n");
			return GMACD_PARAM;
		}

		RING_DEC(idx, q->tx_size);

		/* Reset TX callback */
		if (q->tx_callbacks)
			q->tx_callbacks[idx] = NULL;

		desc = &q->tx_desc[idx];

		/* Copy data into transmittion buffer */
		if (sg->buffer && sg->size) {
			memcpy((void*)desc->addr, sg->buffer, sg->size);
			l2cc_clean_region(desc->addr, desc->addr + sg->size);
		}

		/* Compute buffer descriptor status word */
		status = sg->size & GMAC_RX_STATUS_LENGTH_MASK;
		if (i == (sgl->size - 1)) {
			status |= GMAC_TX_STATUS_LASTBUF;
			if (q->tx_callbacks)
				q->tx_callbacks[idx] = callback;
		}
		if (idx == (q->tx_size - 1)) {
			status |= GMAC_TX_STATUS_WRAP;
		}

		/* Update buffer descriptor status word: clear USED bit */
		desc->status = status;
		DSB();
	}

	/* Update TX ring buffer pointers */
	q->tx_head = tx_head;

	/* Now start to transmit if it is not already done */
	gmac_start_transmission(gmac);

	return GMACD_OK;
}

/**
 * \brief Send a packet with GMAC. If the packet size is larger than transfer buffer size
 * error returned. If packet transfer status is monitored, specify callback for each packet.
 *  \param gmacd Pointer to GMAC Driver instance.
 *  \param pBuffer   The buffer to be send
 *  \param size     The size of buffer to be send
 *  \param fTxCb Threshold Wakeup callback
 *  \return         OK, Busy or invalid packet
 */
uint8_t gmacd_send(struct _gmacd* gmacd, uint8_t queue, void *buffer,
		uint32_t size, gmacd_callback_t callback)
{
	struct _gmac_sg sg;
	struct _gmac_sg_list sgl;

	/* Init single entry scatter-gather list */
	sg.size = size;
	sg.buffer = buffer;
	sgl.size = 1;
	sgl.entries = &sg;

	return gmacd_send_sg(gmacd, queue, &sgl, callback);
}

/**
 * Return current load of TX.
 * \param gmacd   Pointer to GMAC Driver instance.
 */
uint32_t gmacd_get_tx_load(struct _gmacd* gmacd, uint8_t queue)
{
	struct _gmacd_queue* q = &gmacd->queues[queue];
	return RING_CNT(q->tx_head, q->tx_tail, q->tx_size);
}

/**
 * \brief Receive a packet with GMAC.
 * If not enough buffer for the packet, the remaining data is lost but right
 * frame length is returned.
 *  \param gmacd Pointer to GMAC Driver instance.
 *  \param pFrame           Buffer to store the frame
 *  \param frameSize        Size of the frame
 *  \param pRcvSize         Received size
 *  \return                 OK, no data, or frame too small
 */
uint8_t gmacd_poll(struct _gmacd* gmacd, uint8_t queue,
	uint8_t* buffer, uint32_t buffer_size, uint32_t* recv_size)
{
	struct _gmacd_queue* q = &gmacd->queues[queue];
	struct _gmac_desc *desc;
	uint32_t idx;
	uint32_t cur_frame_size = 0;
	uint8_t *cur_frame = 0;

	if (!buffer)
		return GMACD_PARAM;

	/* Set the default return value */
	*recv_size = 0;

	/* Process RX descriptors */
	idx = q->rx_head;
	desc = &q->rx_desc[idx];
	while (desc->addr & GMAC_RX_ADDR_OWN) {
		/* A start of frame has been received, discard previous fragments */
		if (desc->status & GMAC_RX_STATUS_SOF) {
			/* Skip previous fragment */
			while (idx != q->rx_head) {
				desc = &q->rx_desc[q->rx_head];
				desc->addr &= ~GMAC_RX_ADDR_OWN;
				RING_INC(q->rx_head, q->rx_size);
			}
			cur_frame = buffer;
			cur_frame_size = 0;
		}

		/* Increment the index */
		RING_INC(idx, q->rx_size);

		/* Copy data in the frame buffer */
		if (cur_frame) {
			if (idx == q->rx_head) {
				trace_info("no EOF (buffers probably too small)\r\n");

				do {
					desc = &q->rx_desc[q->rx_head];
					desc->addr &= ~GMAC_RX_ADDR_OWN;
					RING_INC(q->rx_head, q->rx_size);
				} while (idx != q->rx_head);
				return GMACD_RX_NULL;
			}

			/* Copy the buffer into the application frame */
			uint32_t length = GMAC_RX_UNITSIZE;
			if ((cur_frame_size + length) > buffer_size) {
				length = buffer_size - cur_frame_size;
			}

			uint32_t addr = desc->addr & GMAC_RX_ADDR_MASK;
			l2cc_invalidate_region(addr, addr + length);
			memcpy(cur_frame, (void*)addr, length);
			cur_frame += length;
			cur_frame_size += length;

			/* An end of frame has been received, return the data */
			if (desc->status & GMAC_RX_STATUS_EOF) {
				/* Frame size from the GMAC */
				*recv_size = desc->status & GMAC_RX_STATUS_LENGTH_MASK;

				/* Application frame buffer is too small all
				 * data have not been copied */
				if (cur_frame_size < *recv_size) {
					return GMACD_SIZE_TOO_SMALL;
				}

				/* All data have been copied in the application
				 * frame buffer => release descriptors */
				while (q->rx_head != idx) {
					desc = &q->rx_desc[q->rx_head];
					desc->addr &= ~GMAC_RX_ADDR_OWN;
					RING_INC(q->rx_head, q->rx_size);
				}

				return GMACD_OK;
			}
		}

		/* SOF has not been detected, skip the fragment */
		else {
			desc->addr &= ~GMAC_RX_ADDR_OWN;
			q->rx_head = idx;
		}

		/* Process the next buffer */
		desc = &q->rx_desc[idx];
	}
	return GMACD_RX_NULL;
}

/**
 * \brief Registers pRxCb callback. Callback will be invoked after the next received
 * frame. When GMAC_Poll() returns GMAC_RX_NO_DATA the application task call GMAC_Set_RxCb()
 * to register pRxCb() callback and enters suspend state. The callback is in charge
 * to resume the task once a new frame has been received. The next time GMAC_Poll()
 * is called, it will be successful.
 *  \param gmacd Pointer to GMAC Driver instance.
 *  \param fRxCb   Pointer to callback function
 *  \return        OK, no data, or frame too small
 */

void gmacd_set_rx_callback(struct _gmacd* gmacd, uint8_t queue, gmacd_callback_t callback)
{
	struct _gmacd_queue* q = &gmacd->queues[queue];
	if (!callback) {
		gmac_disable_it(gmacd->gmac, queue, GMAC_IDR_RCOMP);
		q->rx_callback = NULL;
	} else {
		q->rx_callback = callback;
		gmac_enable_it(gmacd->gmac, queue, GMAC_IER_RCOMP);
	}
}

/**
 * Register/Clear TX wakeup callback.
 *
 * When GMACD_Send() returns GMACD_TX_BUSY (all TD busy) the application
 * task calls GMACD_SetTxWakeupCallback() to register fWakeup() callback and
 * enters suspend state. The callback is in charge to resume the task once
 * several TD have been released. The next time GMACD_Send() will be called,
 * it shall be successful.
 *
 * This function is usually invoked with NULL callback from the TX wakeup
 * callback itself, to unregister. Once the callback has resumed the
 * application task, there is no need to invoke the callback again.
 *
 * \param gmacd   Pointer to GMAC Driver instance.
 * \param fWakeup     Wakeup callback.
 * \param bThreshold  Number of free TD before wakeup callback invoked.
 * \return GMACD_OK, GMACD_PARAM on parameter error.
 */
uint8_t gmacd_set_tx_wakeup_callback(struct _gmacd* gmacd, uint8_t queue,
			  gmacd_wakeup_cb_t callback, uint16_t threshold)
{
	struct _gmacd_queue* q = &gmacd->queues[queue];
	if (!callback) {
		q->tx_wakeup_callback = NULL;
	} else {
		if (threshold <= q->tx_size) {
			q->tx_wakeup_callback = callback;
			q->tx_wakeup_threshold = threshold;
		} else {
			return GMACD_PARAM;
		}
	}

	return GMACD_OK;
}

/**@}*/
