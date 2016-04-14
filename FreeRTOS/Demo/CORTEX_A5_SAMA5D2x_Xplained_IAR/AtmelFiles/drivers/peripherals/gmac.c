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

/*----------------------------------------------------------------------------
 *        Headers
 *----------------------------------------------------------------------------*/

#include "chip.h"
#include "trace.h"
#include "peripherals/gmac.h"
#include "peripherals/pmc.h"
#include <stdio.h>
#include <string.h>
#include <assert.h>

/*----------------------------------------------------------------------------
 *        Local definitions
 *----------------------------------------------------------------------------*/

/* some IP versions don't have this configuration flag and instead expect 0 */
#ifndef GMAC_NCFGR_DBW_DBW32
#define GMAC_NCFGR_DBW_DBW32 0
#endif

/* some IP versions don't have this error flag, set it to 0 to ignore it */
#ifndef GMAC_TSR_UND
#define GMAC_TSR_UND 0
#endif

/*----------------------------------------------------------------------------
 *        Local functions
 *----------------------------------------------------------------------------*/

static bool _gmac_configure_mdc_clock(Gmac *gmac)
{
	uint32_t mck, clk;

	mck = pmc_get_peripheral_clock(get_gmac_id_from_addr(gmac));

	/* Disable RX/TX */
	gmac->GMAC_NCR &= ~(GMAC_NCR_RXEN | GMAC_NCR_TXEN);

	/* Find divider */
	if (mck <= 20000000) {
		clk = GMAC_NCFGR_CLK_MCK_8; // MCK/8
	} else if (mck <= 40000000) {
		clk = GMAC_NCFGR_CLK_MCK_16; // MCK/16
	} else if (mck <= 80000000) {
		clk = GMAC_NCFGR_CLK_MCK_32; // MCK/32
	} else if (mck <= 120000000) {
		clk = GMAC_NCFGR_CLK_MCK_48; // MCK/48
	} else if (mck <= 160000000) {
		clk = GMAC_NCFGR_CLK_MCK_64; // MCK/64
	} else if (mck <= 240000000) {
		clk = GMAC_NCFGR_CLK_MCK_96; // MCK/96
	} else {
		trace_error("MCK too high, cannot configure MDC clock.\r\n");
		return false;
	}

	/* configure MDC clock divider and enable RX/TX */
	gmac->GMAC_NCFGR = (gmac->GMAC_NCFGR & ~GMAC_NCFGR_CLK_Msk) | clk;
	gmac->GMAC_NCR |= (GMAC_NCR_RXEN | GMAC_NCR_TXEN);

	return true;
}

static bool _gmac_phy_wait_idle(Gmac* gmac, uint32_t retries)
{
	uint32_t count = 0;
	while ((gmac->GMAC_NSR & GMAC_NSR_IDLE) == 0) {
		if (retries > 0 && count > retries) {
			trace_debug("Timeout reached while waiting for PHY management logic to become idle");
			return false;
		}
		count++;
	}
	return true;
}

static void _gmac_set_link_speed(Gmac* gmac, enum _gmac_speed speed, enum _gmac_duplex duplex)
{
	/* Configure duplex */
	switch (duplex) {
	case GMAC_DUPLEX_HALF:
		gmac->GMAC_NCFGR &= ~GMAC_NCFGR_FD;
		break;
	case GMAC_DUPLEX_FULL:
		gmac->GMAC_NCFGR |= GMAC_NCFGR_FD;
		break;
	default:
		trace_error("Invalid duplex value %d\r\n", duplex);
		return;
	}

	/* Configure speed */
	switch (speed) {
	case GMAC_SPEED_10M:
		gmac->GMAC_NCFGR &= ~GMAC_NCFGR_SPD;
		break;
	case GMAC_SPEED_100M:
		gmac->GMAC_NCFGR |= GMAC_NCFGR_SPD;
		break;
	default:
		trace_error("Invalid speed value %d\r\n", speed);
		return;
	}
}

/*----------------------------------------------------------------------------
 *        Exported functions
 *----------------------------------------------------------------------------*/

bool gmac_configure(Gmac* gmac)
{
	pmc_enable_peripheral(get_gmac_id_from_addr(gmac));

	/* Disable TX & RX and more */
	gmac_set_network_control_register(gmac, 0);
	gmac_set_network_config_register(gmac, GMAC_NCFGR_DBW_DBW32);

	/* Disable interrupts */
	gmac_disable_it(gmac, 0, ~0u);
#ifdef CONFIG_HAVE_GMAC_QUEUES
	gmac_disable_it(gmac, 1, ~0u);
	gmac_disable_it(gmac, 2, ~0u);
#endif

	/* Clear statistics */
	gmac_clear_statistics(gmac);

	/* Clear all status bits in the receive status register. */
	gmac_clear_rx_status(gmac, GMAC_RSR_RXOVR | GMAC_RSR_REC |
			GMAC_RSR_BNA | GMAC_RSR_HNO);

	/* Clear all status bits in the transmit status register */
	gmac_clear_tx_status(gmac, GMAC_TSR_UBR | GMAC_TSR_COL |
			GMAC_TSR_RLE | GMAC_TSR_TXGO | GMAC_TSR_TFC |
			GMAC_TSR_TXCOMP | GMAC_TSR_UND | GMAC_TSR_HRESP);

	/* Clear interrupts */
	gmac_get_it_status(gmac, 0);
#ifdef CONFIG_HAVE_GMAC_QUEUES
	gmac_get_it_status(gmac, 1);
	gmac_get_it_status(gmac, 2);
#endif

	return _gmac_configure_mdc_clock(gmac);
}

void gmac_set_network_control_register(Gmac* gmac, uint32_t ncr)
{
	gmac->GMAC_NCR = ncr;
}

uint32_t gmac_get_network_control_register(Gmac* gmac)
{
	return gmac->GMAC_NCR;
}

void gmac_set_network_config_register(Gmac* gmac, uint32_t ncfgr)
{
	gmac->GMAC_NCFGR = ncfgr;
}

uint32_t gmac_get_network_config_register(Gmac* gmac)
{
	return gmac->GMAC_NCFGR;
}

void gmac_enable_mdio(Gmac* gmac)
{
	/* Disable RX/TX */
	gmac->GMAC_NCR &= ~(GMAC_NCR_RXEN | GMAC_NCR_TXEN);

	/* Enable MDIO */
	gmac->GMAC_NCR |= GMAC_NCR_MPE;

	/* Enable RX/TX */
	gmac->GMAC_NCR |= (GMAC_NCR_RXEN | GMAC_NCR_TXEN);
}

void gmac_disable_mdio(Gmac* gmac)
{
	/* Disable RX/TX */
	gmac->GMAC_NCR &= ~(GMAC_NCR_RXEN | GMAC_NCR_TXEN);

	/* Disable MDIO */
	gmac->GMAC_NCR &= ~GMAC_NCR_MPE;

	/* Enable RX/TX */
	gmac->GMAC_NCR |= (GMAC_NCR_RXEN | GMAC_NCR_TXEN);
}

bool gmac_phy_read(Gmac* gmac, uint8_t phy_addr, uint8_t reg_addr, uint16_t* data,
		uint32_t retries)
{
	/* Wait until idle */
	if (!_gmac_phy_wait_idle(gmac, retries))
		return false;

	/* Write maintenance register */
	gmac->GMAC_MAN = GMAC_MAN_CLTTO |
		GMAC_MAN_OP(2) |
		GMAC_MAN_WTN(2) |
		GMAC_MAN_PHYA(phy_addr) |
		GMAC_MAN_REGA(reg_addr);

	/* Wait until idle */
	if (!_gmac_phy_wait_idle(gmac, retries))
		return false;

	*data = (gmac->GMAC_MAN & GMAC_MAN_DATA_Msk) >> GMAC_MAN_DATA_Pos;
	return true;
}

bool gmac_phy_write(Gmac* gmac, uint8_t phy_addr, uint8_t reg_addr, uint16_t data,
		uint32_t retries)
{
	/* Wait until idle */
	if (!_gmac_phy_wait_idle(gmac, retries))
		return false;

	/* Write maintenance register */
	gmac->GMAC_MAN = GMAC_MAN_CLTTO |
		GMAC_MAN_OP(1) |
		GMAC_MAN_WTN(2) |
		GMAC_MAN_PHYA(phy_addr) |
		GMAC_MAN_REGA(reg_addr) |
		GMAC_MAN_DATA(data);

	/* Wait until idle */
	return _gmac_phy_wait_idle(gmac, retries);
}

void gmac_enable_mii(Gmac* gmac)
{
	/* Disable RX/TX */
	gmac->GMAC_NCR &= ~(GMAC_NCR_RXEN | GMAC_NCR_TXEN);

	/* Disable RMII */
	gmac->GMAC_UR &= ~GMAC_UR_RMII;

	/* Enable RX/TX */
	gmac->GMAC_NCR |= (GMAC_NCR_RXEN | GMAC_NCR_TXEN);
}

void gmac_enable_rmii(Gmac* gmac, enum _gmac_speed speed, enum _gmac_duplex duplex)
{
	/* Disable RX/TX */
	gmac->GMAC_NCR &= ~(GMAC_NCR_RXEN | GMAC_NCR_TXEN);

	/* Configure speed/duplex */
	_gmac_set_link_speed(gmac, speed, duplex);

	/* Enable RMII */
	gmac->GMAC_UR |= GMAC_UR_RMII;

	/* Enable RX/TX */
	gmac->GMAC_NCR |= (GMAC_NCR_RXEN | GMAC_NCR_TXEN);
}

void gmac_set_link_speed(Gmac* gmac, enum _gmac_speed speed, enum _gmac_duplex duplex)
{
	/* Disable RX/TX */
	gmac->GMAC_NCR &= ~(GMAC_NCR_RXEN | GMAC_NCR_TXEN);

	/* Configure speed/duplex */
	_gmac_set_link_speed(gmac, speed, duplex);

	/* Enable RX/TX */
	gmac->GMAC_NCR |= (GMAC_NCR_RXEN | GMAC_NCR_TXEN);
}

void gmac_enable_local_loopback(Gmac* gmac)
{
	gmac->GMAC_NCR |= GMAC_NCR_LBL;
}

void gmac_disable_local_loopback(Gmac* gmac)
{
	gmac->GMAC_NCR &= ~GMAC_NCR_LBL;
}

uint32_t gmac_get_tx_status(Gmac* gmac)
{
	return gmac->GMAC_TSR;
}

void gmac_clear_tx_status(Gmac* gmac, uint32_t mask)
{
	gmac->GMAC_TSR = mask;
}

uint32_t gmac_get_rx_status(Gmac* gmac)
{
	return gmac->GMAC_RSR;
}

void gmac_clear_rx_status(Gmac* gmac, uint32_t mask)
{
	gmac->GMAC_RSR = mask;
}

void gmac_receive_enable(Gmac* gmac, bool enable)
{
	if (enable)
		gmac->GMAC_NCR |= GMAC_NCR_RXEN;
	else
		gmac->GMAC_NCR &= ~GMAC_NCR_RXEN;
}

void gmac_transmit_enable(Gmac* gmac, bool enable)
{
	if (enable)
		gmac->GMAC_NCR |= GMAC_NCR_TXEN;
	else
		gmac->GMAC_NCR &= ~GMAC_NCR_TXEN;
}

void gmac_set_rx_desc(Gmac* gmac, uint8_t queue, struct _gmac_desc* desc)
{
	if (queue == 0) {
		gmac->GMAC_RBQB = ((uint32_t)desc) & GMAC_RBQB_ADDR_Msk;
	}
#ifdef CONFIG_HAVE_GMAC_QUEUES
	else if (queue <= GMAC_NUM_QUEUES) {
		gmac->GMAC_RBQBAPQ[queue - 1] = ((uint32_t)desc) & GMAC_RBQBAPQ_RXBQBA_Msk;
	}
#endif
	else {
		trace_debug("Invalid queue number %d\r\n", queue);
	}
}

struct _gmac_desc* gmac_get_rx_desc(Gmac* gmac, uint8_t queue)
{
	if (queue == 0) {
		return (struct _gmac_desc*)(gmac->GMAC_RBQB & GMAC_RBQB_ADDR_Msk);
	}
#ifdef CONFIG_HAVE_GMAC_QUEUES
	else if (queue <= GMAC_NUM_QUEUES) {
		return (struct _gmac_desc*)(gmac->GMAC_RBQBAPQ[queue - 1] & GMAC_RBQBAPQ_RXBQBA_Msk);
	}
#endif
	else {
		trace_debug("Invalid queue number %d\r\n", queue);
		return NULL;
	}
}

void gmac_set_tx_desc(Gmac* gmac, uint8_t queue, struct _gmac_desc* desc)
{
	if (queue == 0) {
		gmac->GMAC_TBQB = ((uint32_t)desc) & GMAC_TBQB_ADDR_Msk;
	}
#ifdef CONFIG_HAVE_GMAC_QUEUES
	else if (queue <= GMAC_NUM_QUEUES) {
		gmac->GMAC_TBQBAPQ[queue - 1] = ((uint32_t)desc) & GMAC_TBQBAPQ_TXBQBA_Msk;
	}
#endif
	else {
		trace_debug("Invalid queue number %d\r\n", queue);
	}
}

struct _gmac_desc* gmac_get_tx_desc(Gmac* gmac, uint8_t queue)
{
	if (queue == 0) {
		return (struct _gmac_desc*)(gmac->GMAC_TBQB & GMAC_TBQB_ADDR_Msk);
	}
#ifdef CONFIG_HAVE_GMAC_QUEUES
	else if (queue <= GMAC_NUM_QUEUES) {
		return (struct _gmac_desc*)(gmac->GMAC_TBQBAPQ[queue - 1] & GMAC_TBQBAPQ_TXBQBA_Msk);
	}
#endif
	else {
		trace_debug("Invalid queue number %d\r\n", queue);
		return NULL;
	}
}

uint32_t gmac_get_it_mask(Gmac* gmac, uint8_t queue)
{
	if (queue == 0) {
		return gmac->GMAC_IMR;
	}
#ifdef CONFIG_HAVE_GMAC_QUEUES
	else if (queue <= GMAC_NUM_QUEUES) {
		return gmac->GMAC_IMRPQ[queue - 1];
	}
#endif
	else {
		trace_debug("Invalid queue number %d\r\n", queue);
		return 0;
	}
}

void gmac_enable_it(Gmac* gmac, uint8_t queue, uint32_t mask)
{
	if (queue == 0) {
		gmac->GMAC_IER = mask;
	}
#ifdef CONFIG_HAVE_GMAC_QUEUES
	else if (queue <= GMAC_NUM_QUEUES) {
		gmac->GMAC_IERPQ[queue - 1] = mask;
	}
#endif
	else {
		trace_debug("Invalid queue number %d\r\n", queue);
	}
}

void gmac_disable_it(Gmac * gmac, uint8_t queue, uint32_t mask)
{
	if (queue == 0) {
		gmac->GMAC_IDR = mask;
	}
#ifdef CONFIG_HAVE_GMAC_QUEUES
	else if (queue <= GMAC_NUM_QUEUES) {
		gmac->GMAC_IDRPQ[queue - 1] = mask;
	}
#endif
	else {
		trace_debug("Invalid queue number %d\r\n", queue);
	}
}

uint32_t gmac_get_it_status(Gmac* gmac, uint8_t queue)
{
	if (queue == 0) {
		return gmac->GMAC_ISR;
	}
#ifdef CONFIG_HAVE_GMAC_QUEUES
	else if (queue <= GMAC_NUM_QUEUES) {
		return gmac->GMAC_ISRPQ[queue - 1];
	}
#endif
	else {
		trace_debug("Invalid queue number %d\r\n", queue);
		return 0;
	}
}

void gmac_set_mac_addr(Gmac* gmac, uint8_t sa_idx, uint8_t* mac)
{
	gmac->GMAC_SA[sa_idx].GMAC_SAB = (mac[3] << 24) |
		(mac[2] << 16) | (mac[1] << 8) | mac[0];
	gmac->GMAC_SA[sa_idx].GMAC_SAT = (mac[5] << 8) |
		mac[4];
}

void gmac_set_mac_addr32(Gmac* gmac, uint8_t sa_idx,
			 uint32_t mac_top, uint32_t mac_bottom)
{
	gmac->GMAC_SA[sa_idx].GMAC_SAB = mac_bottom;
	gmac->GMAC_SA[sa_idx].GMAC_SAT = mac_top;
}

void gmac_set_mac_addr64(Gmac* gmac, uint8_t sa_idx, uint64_t mac)
{
	gmac->GMAC_SA[sa_idx].GMAC_SAB = (uint32_t)(mac & 0xffffffff);
	gmac->GMAC_SA[sa_idx].GMAC_SAT = (uint32_t)(mac >> 32);
}

void gmac_clear_statistics(Gmac* gmac)
{
	gmac->GMAC_NCR |= GMAC_NCR_CLRSTAT;
}

void gmac_increase_statistics(Gmac* gmac)
{
	gmac->GMAC_NCR |= GMAC_NCR_INCSTAT;
}

void gmac_enable_statistics_write(Gmac* gmac, bool enable)
{
	if (enable)
		gmac->GMAC_NCR |= GMAC_NCR_WESTAT;
	else
		gmac->GMAC_NCR &= ~GMAC_NCR_WESTAT;
}

void gmac_start_transmission(Gmac * gmac)
{
	gmac->GMAC_NCR |= GMAC_NCR_TSTART;
}

void gmac_halt_transmission(Gmac * gmac)
{
	gmac->GMAC_NCR |= GMAC_NCR_THALT;
}
